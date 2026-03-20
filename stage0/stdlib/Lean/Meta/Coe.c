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
size_t v_x_36296__boxed_239_; uint8_t v_res_240_; lean_object* v_r_241_; 
v_x_36296__boxed_239_ = lean_unbox_usize(v_x_237_);
lean_dec(v_x_237_);
v_res_240_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_236_, v_x_36296__boxed_239_, v_x_238_);
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
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
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
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
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
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
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
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
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
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___lam__0(lean_object* v_k_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v_b_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = lean_apply_8(v_k_770_, v_b_773_, v___y_771_, v___y_772_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, lean_box(0));
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___lam__0___boxed(lean_object* v_k_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___lam__0(v_k_780_, v___y_781_, v___y_782_, v_b_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___redArg(lean_object* v_name_790_, lean_object* v_type_791_, lean_object* v_val_792_, lean_object* v_k_793_, uint8_t v_nondep_794_, uint8_t v_kind_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___f_803_; lean_object* v___x_804_; 
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
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg(lean_object* v_name_837_, uint8_t v_bi_838_, lean_object* v_type_839_, lean_object* v_k_840_, uint8_t v_kind_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___f_849_; lean_object* v___x_850_; 
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
lean_object* v___y_1066_; lean_object* v_fileName_1083_; lean_object* v_fileMap_1084_; lean_object* v_options_1085_; lean_object* v_currRecDepth_1086_; lean_object* v_maxRecDepth_1087_; lean_object* v_ref_1088_; lean_object* v_currNamespace_1089_; lean_object* v_openDecls_1090_; lean_object* v_initHeartbeats_1091_; lean_object* v_maxHeartbeats_1092_; lean_object* v_quotContext_1093_; lean_object* v_currMacroScope_1094_; uint8_t v_diag_1095_; lean_object* v_cancelTk_x3f_1096_; uint8_t v_suppressElabErrors_1097_; lean_object* v_inheritedTraceOptions_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1110_; 
v_fileName_1083_ = lean_ctor_get(v___y_1062_, 0);
v_fileMap_1084_ = lean_ctor_get(v___y_1062_, 1);
v_options_1085_ = lean_ctor_get(v___y_1062_, 2);
v_currRecDepth_1086_ = lean_ctor_get(v___y_1062_, 3);
v_maxRecDepth_1087_ = lean_ctor_get(v___y_1062_, 4);
v_ref_1088_ = lean_ctor_get(v___y_1062_, 5);
v_currNamespace_1089_ = lean_ctor_get(v___y_1062_, 6);
v_openDecls_1090_ = lean_ctor_get(v___y_1062_, 7);
v_initHeartbeats_1091_ = lean_ctor_get(v___y_1062_, 8);
v_maxHeartbeats_1092_ = lean_ctor_get(v___y_1062_, 9);
v_quotContext_1093_ = lean_ctor_get(v___y_1062_, 10);
v_currMacroScope_1094_ = lean_ctor_get(v___y_1062_, 11);
v_diag_1095_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*14);
v_cancelTk_x3f_1096_ = lean_ctor_get(v___y_1062_, 12);
v_suppressElabErrors_1097_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1098_ = lean_ctor_get(v___y_1062_, 13);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___y_1062_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1100_ = v___y_1062_;
v_isShared_1101_ = v_isSharedCheck_1110_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_inheritedTraceOptions_1098_);
lean_inc(v_cancelTk_x3f_1096_);
lean_inc(v_currMacroScope_1094_);
lean_inc(v_quotContext_1093_);
lean_inc(v_maxHeartbeats_1092_);
lean_inc(v_initHeartbeats_1091_);
lean_inc(v_openDecls_1090_);
lean_inc(v_currNamespace_1089_);
lean_inc(v_ref_1088_);
lean_inc(v_maxRecDepth_1087_);
lean_inc(v_currRecDepth_1086_);
lean_inc(v_options_1085_);
lean_inc(v_fileMap_1084_);
lean_inc(v_fileName_1083_);
lean_dec(v___y_1062_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1110_;
goto v_resetjp_1099_;
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
v_resetjp_1099_:
{
uint8_t v___x_1102_; 
v___x_1102_ = lean_nat_dec_eq(v_currRecDepth_1086_, v_maxRecDepth_1087_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_add(v_currRecDepth_1086_, v___x_1103_);
lean_dec(v_currRecDepth_1086_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 3, v___x_1104_);
v___x_1106_ = v___x_1100_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_fileName_1083_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_fileMap_1084_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_options_1085_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_maxRecDepth_1087_);
lean_ctor_set(v_reuseFailAlloc_1108_, 5, v_ref_1088_);
lean_ctor_set(v_reuseFailAlloc_1108_, 6, v_currNamespace_1089_);
lean_ctor_set(v_reuseFailAlloc_1108_, 7, v_openDecls_1090_);
lean_ctor_set(v_reuseFailAlloc_1108_, 8, v_initHeartbeats_1091_);
lean_ctor_set(v_reuseFailAlloc_1108_, 9, v_maxHeartbeats_1092_);
lean_ctor_set(v_reuseFailAlloc_1108_, 10, v_quotContext_1093_);
lean_ctor_set(v_reuseFailAlloc_1108_, 11, v_currMacroScope_1094_);
lean_ctor_set(v_reuseFailAlloc_1108_, 12, v_cancelTk_x3f_1096_);
lean_ctor_set(v_reuseFailAlloc_1108_, 13, v_inheritedTraceOptions_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*14, v_diag_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*14 + 1, v_suppressElabErrors_1097_);
v___x_1106_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_apply_7(v_x_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___x_1106_, v___y_1063_, lean_box(0));
v___y_1066_ = v___x_1107_;
goto v___jp_1065_;
}
}
else
{
lean_object* v___x_1109_; 
lean_del_object(v___x_1100_);
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
lean_dec(v___y_1063_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v_x_1057_);
v___x_1109_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg(v_ref_1088_);
v___y_1066_ = v___x_1109_;
goto v___jp_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg___boxed(lean_object* v_x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_x_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg(lean_object* v_a_1120_, lean_object* v_x_1121_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_box(0);
return v___x_1122_;
}
else
{
lean_object* v_key_1123_; lean_object* v_value_1124_; lean_object* v_tail_1125_; uint8_t v___x_1126_; 
v_key_1123_ = lean_ctor_get(v_x_1121_, 0);
v_value_1124_ = lean_ctor_get(v_x_1121_, 1);
v_tail_1125_ = lean_ctor_get(v_x_1121_, 2);
v___x_1126_ = l_Lean_ExprStructEq_beq(v_key_1123_, v_a_1120_);
if (v___x_1126_ == 0)
{
v_x_1121_ = v_tail_1125_;
goto _start;
}
else
{
lean_object* v___x_1128_; 
lean_inc(v_value_1124_);
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_value_1124_);
return v___x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_a_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg(v_a_1129_, v_x_1130_);
lean_dec(v_x_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(lean_object* v_m_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_buckets_1134_; lean_object* v___x_1135_; uint64_t v___x_1136_; uint64_t v___x_1137_; uint64_t v___x_1138_; uint64_t v_fold_1139_; uint64_t v___x_1140_; uint64_t v___x_1141_; uint64_t v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; size_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v_buckets_1134_ = lean_ctor_get(v_m_1132_, 1);
v___x_1135_ = lean_array_get_size(v_buckets_1134_);
v___x_1136_ = l_Lean_ExprStructEq_hash(v_a_1133_);
v___x_1137_ = 32ULL;
v___x_1138_ = lean_uint64_shift_right(v___x_1136_, v___x_1137_);
v_fold_1139_ = lean_uint64_xor(v___x_1136_, v___x_1138_);
v___x_1140_ = 16ULL;
v___x_1141_ = lean_uint64_shift_right(v_fold_1139_, v___x_1140_);
v___x_1142_ = lean_uint64_xor(v_fold_1139_, v___x_1141_);
v___x_1143_ = lean_uint64_to_usize(v___x_1142_);
v___x_1144_ = lean_usize_of_nat(v___x_1135_);
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_sub(v___x_1144_, v___x_1145_);
v___x_1147_ = lean_usize_land(v___x_1143_, v___x_1146_);
v___x_1148_ = lean_array_uget_borrowed(v_buckets_1134_, v___x_1147_);
v___x_1149_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg(v_a_1133_, v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___boxed(lean_object* v_m_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_m_1150_, v_a_1151_);
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_m_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1153_, lean_object* v_x_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_apply_1(v_x_1154_, lean_box(0));
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v___y_1155_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1164_, v_x_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1175_, lean_object* v_pre_1176_, lean_object* v_post_1177_, uint8_t v_usedLetOnly_1178_, uint8_t v_skipConstInApp_1179_, uint8_t v_skipInstances_1180_, lean_object* v_body_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_array_push(v_fvars_1175_, v_x_1182_);
v___x_1191_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1176_, v_post_1177_, v_usedLetOnly_1178_, v_skipConstInApp_1179_, v_skipInstances_1180_, v___x_1190_, v_body_1181_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1192_, lean_object* v_pre_1193_, lean_object* v_post_1194_, lean_object* v_usedLetOnly_1195_, lean_object* v_skipConstInApp_1196_, lean_object* v_skipInstances_1197_, lean_object* v_body_1198_, lean_object* v_x_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v_usedLetOnly_boxed_1207_; uint8_t v_skipConstInApp_boxed_1208_; uint8_t v_skipInstances_boxed_1209_; lean_object* v_res_1210_; 
v_usedLetOnly_boxed_1207_ = lean_unbox(v_usedLetOnly_1195_);
v_skipConstInApp_boxed_1208_ = lean_unbox(v_skipConstInApp_1196_);
v_skipInstances_boxed_1209_ = lean_unbox(v_skipInstances_1197_);
v_res_1210_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1192_, v_pre_1193_, v_post_1194_, v_usedLetOnly_boxed_1207_, v_skipConstInApp_boxed_1208_, v_skipInstances_boxed_1209_, v_body_1198_, v_x_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_pre_1211_, lean_object* v_post_1212_, uint8_t v_usedLetOnly_1213_, uint8_t v_skipConstInApp_1214_, uint8_t v_skipInstances_1215_, lean_object* v_e_1216_, lean_object* v_a_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
lean_inc_ref(v_post_1212_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
lean_inc_ref(v_e_1216_);
v___x_1224_ = lean_apply_7(v_post_1212_, v_e_1216_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, lean_box(0));
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1256_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1256_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1256_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1255_; 
v_fst_1229_ = lean_ctor_get(v_a_1225_, 0);
v_snd_1230_ = lean_ctor_get(v_a_1225_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_a_1225_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1232_ = v_a_1225_;
v_isShared_1233_ = v_isSharedCheck_1255_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_snd_1230_);
lean_inc(v_fst_1229_);
lean_dec(v_a_1225_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1255_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___y_1235_; 
switch(lean_obj_tag(v_fst_1229_))
{
case 0:
{
lean_object* v_e_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
lean_del_object(v___x_1232_);
lean_del_object(v___x_1227_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v_a_1217_);
lean_dec_ref(v_e_1216_);
lean_dec_ref(v_post_1212_);
lean_dec_ref(v_pre_1211_);
v_e_1242_ = lean_ctor_get(v_fst_1229_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_fst_1229_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1244_ = v_fst_1229_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_e_1242_);
lean_dec(v_fst_1229_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_e_1242_);
lean_ctor_set(v___x_1246_, 1, v_snd_1230_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
case 1:
{
lean_object* v_e_1251_; lean_object* v___x_1252_; 
lean_del_object(v___x_1232_);
lean_del_object(v___x_1227_);
lean_dec_ref(v_e_1216_);
v_e_1251_ = lean_ctor_get(v_fst_1229_, 0);
lean_inc_ref(v_e_1251_);
lean_dec_ref(v_fst_1229_);
v___x_1252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1211_, v_post_1212_, v_usedLetOnly_1213_, v_skipConstInApp_1214_, v_skipInstances_1215_, v_e_1251_, v_a_1217_, v_snd_1230_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1252_;
}
default: 
{
lean_object* v_e_x3f_1253_; 
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v_a_1217_);
lean_dec_ref(v_post_1212_);
lean_dec_ref(v_pre_1211_);
v_e_x3f_1253_ = lean_ctor_get(v_fst_1229_, 0);
lean_inc(v_e_x3f_1253_);
lean_dec_ref(v_fst_1229_);
if (lean_obj_tag(v_e_x3f_1253_) == 0)
{
v___y_1235_ = v_e_1216_;
goto v___jp_1234_;
}
else
{
lean_object* v_val_1254_; 
lean_dec_ref(v_e_1216_);
v_val_1254_ = lean_ctor_get(v_e_x3f_1253_, 0);
lean_inc(v_val_1254_);
lean_dec_ref(v_e_x3f_1253_);
v___y_1235_ = v_val_1254_;
goto v___jp_1234_;
}
}
}
v___jp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___y_1235_);
v___x_1237_ = v___x_1232_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___y_1235_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_snd_1230_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1237_);
v___x_1239_ = v___x_1227_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v_a_1217_);
lean_dec_ref(v_e_1216_);
lean_dec_ref(v_post_1212_);
lean_dec_ref(v_pre_1211_);
v_a_1257_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1224_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1224_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1265_, lean_object* v_post_1266_, uint8_t v_usedLetOnly_1267_, uint8_t v_skipConstInApp_1268_, uint8_t v_skipInstances_1269_, lean_object* v_fvars_1270_, lean_object* v_e_1271_, lean_object* v_a_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
if (lean_obj_tag(v_e_1271_) == 6)
{
lean_object* v_binderName_1279_; lean_object* v_binderType_1280_; lean_object* v_body_1281_; uint8_t v_binderInfo_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_binderName_1279_ = lean_ctor_get(v_e_1271_, 0);
lean_inc(v_binderName_1279_);
v_binderType_1280_ = lean_ctor_get(v_e_1271_, 1);
lean_inc_ref(v_binderType_1280_);
v_body_1281_ = lean_ctor_get(v_e_1271_, 2);
lean_inc_ref(v_body_1281_);
v_binderInfo_1282_ = lean_ctor_get_uint8(v_e_1271_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1271_);
v___x_1283_ = lean_expr_instantiate_rev(v_binderType_1280_, v_fvars_1270_);
lean_dec_ref(v_binderType_1280_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v_a_1272_);
lean_inc_ref(v_post_1266_);
lean_inc_ref(v_pre_1265_);
v___x_1284_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1265_, v_post_1266_, v_usedLetOnly_1267_, v_skipConstInApp_1268_, v_skipInstances_1269_, v___x_1283_, v_a_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v_fst_1286_; lean_object* v_snd_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___f_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref(v___x_1284_);
v_fst_1286_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_fst_1286_);
v_snd_1287_ = lean_ctor_get(v_a_1285_, 1);
lean_inc(v_snd_1287_);
lean_dec(v_a_1285_);
v___x_1288_ = lean_box(v_usedLetOnly_1267_);
v___x_1289_ = lean_box(v_skipConstInApp_1268_);
v___x_1290_ = lean_box(v_skipInstances_1269_);
v___f_1291_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1291_, 0, v_fvars_1270_);
lean_closure_set(v___f_1291_, 1, v_pre_1265_);
lean_closure_set(v___f_1291_, 2, v_post_1266_);
lean_closure_set(v___f_1291_, 3, v___x_1288_);
lean_closure_set(v___f_1291_, 4, v___x_1289_);
lean_closure_set(v___f_1291_, 5, v___x_1290_);
lean_closure_set(v___f_1291_, 6, v_body_1281_);
v___x_1292_ = 0;
v___x_1293_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg(v_binderName_1279_, v_binderInfo_1282_, v_fst_1286_, v___f_1291_, v___x_1292_, v_a_1272_, v_snd_1287_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1293_;
}
else
{
lean_dec_ref(v_body_1281_);
lean_dec(v_binderName_1279_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v_a_1272_);
lean_dec_ref(v_fvars_1270_);
lean_dec_ref(v_post_1266_);
lean_dec_ref(v_pre_1265_);
return v___x_1284_;
}
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_expr_instantiate_rev(v_e_1271_, v_fvars_1270_);
lean_dec_ref(v_e_1271_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v_a_1272_);
lean_inc_ref(v_post_1266_);
lean_inc_ref(v_pre_1265_);
v___x_1295_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1265_, v_post_1266_, v_usedLetOnly_1267_, v_skipConstInApp_1268_, v_skipInstances_1269_, v___x_1294_, v_a_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v_fst_1297_; lean_object* v_snd_1298_; uint8_t v___x_1299_; uint8_t v___x_1300_; uint8_t v___x_1301_; lean_object* v___x_1302_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref(v___x_1295_);
v_fst_1297_ = lean_ctor_get(v_a_1296_, 0);
lean_inc(v_fst_1297_);
v_snd_1298_ = lean_ctor_get(v_a_1296_, 1);
lean_inc(v_snd_1298_);
lean_dec(v_a_1296_);
v___x_1299_ = 0;
v___x_1300_ = 1;
v___x_1301_ = 1;
v___x_1302_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1270_, v_fst_1297_, v___x_1299_, v_usedLetOnly_1267_, v___x_1299_, v___x_1300_, v___x_1301_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec_ref(v_fvars_1270_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref(v___x_1302_);
v___x_1304_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1265_, v_post_1266_, v_usedLetOnly_1267_, v_skipConstInApp_1268_, v_skipInstances_1269_, v_a_1303_, v_a_1272_, v_snd_1298_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1304_;
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_snd_1298_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v_a_1272_);
lean_dec_ref(v_post_1266_);
lean_dec_ref(v_pre_1265_);
v_a_1305_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1302_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1302_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v_a_1272_);
lean_dec_ref(v_fvars_1270_);
lean_dec_ref(v_post_1266_);
lean_dec_ref(v_pre_1265_);
return v___x_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(lean_object* v_fvars_1313_, lean_object* v_pre_1314_, lean_object* v_post_1315_, uint8_t v_usedLetOnly_1316_, uint8_t v_skipConstInApp_1317_, uint8_t v_skipInstances_1318_, lean_object* v_body_1319_, lean_object* v_x_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_array_push(v_fvars_1313_, v_x_1320_);
v___x_1329_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1314_, v_post_1315_, v_usedLetOnly_1316_, v_skipConstInApp_1317_, v_skipInstances_1318_, v___x_1328_, v_body_1319_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed(lean_object* v_fvars_1330_, lean_object* v_pre_1331_, lean_object* v_post_1332_, lean_object* v_usedLetOnly_1333_, lean_object* v_skipConstInApp_1334_, lean_object* v_skipInstances_1335_, lean_object* v_body_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
uint8_t v_usedLetOnly_boxed_1345_; uint8_t v_skipConstInApp_boxed_1346_; uint8_t v_skipInstances_boxed_1347_; lean_object* v_res_1348_; 
v_usedLetOnly_boxed_1345_ = lean_unbox(v_usedLetOnly_1333_);
v_skipConstInApp_boxed_1346_ = lean_unbox(v_skipConstInApp_1334_);
v_skipInstances_boxed_1347_ = lean_unbox(v_skipInstances_1335_);
v_res_1348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(v_fvars_1330_, v_pre_1331_, v_post_1332_, v_usedLetOnly_boxed_1345_, v_skipConstInApp_boxed_1346_, v_skipInstances_boxed_1347_, v_body_1336_, v_x_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(lean_object* v_pre_1349_, lean_object* v_post_1350_, uint8_t v_usedLetOnly_1351_, uint8_t v_skipConstInApp_1352_, uint8_t v_skipInstances_1353_, lean_object* v_fvars_1354_, lean_object* v_e_1355_, lean_object* v_a_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
if (lean_obj_tag(v_e_1355_) == 8)
{
lean_object* v_declName_1363_; lean_object* v_type_1364_; lean_object* v_value_1365_; lean_object* v_body_1366_; uint8_t v_nondep_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_declName_1363_ = lean_ctor_get(v_e_1355_, 0);
lean_inc(v_declName_1363_);
v_type_1364_ = lean_ctor_get(v_e_1355_, 1);
lean_inc_ref(v_type_1364_);
v_value_1365_ = lean_ctor_get(v_e_1355_, 2);
lean_inc_ref(v_value_1365_);
v_body_1366_ = lean_ctor_get(v_e_1355_, 3);
lean_inc_ref(v_body_1366_);
v_nondep_1367_ = lean_ctor_get_uint8(v_e_1355_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1355_);
v___x_1368_ = lean_expr_instantiate_rev(v_type_1364_, v_fvars_1354_);
lean_dec_ref(v_type_1364_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v_a_1356_);
lean_inc_ref(v_post_1350_);
lean_inc_ref(v_pre_1349_);
v___x_1369_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1349_, v_post_1350_, v_usedLetOnly_1351_, v_skipConstInApp_1352_, v_skipInstances_1353_, v___x_1368_, v_a_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v_fst_1371_; lean_object* v_snd_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
v_fst_1371_ = lean_ctor_get(v_a_1370_, 0);
lean_inc(v_fst_1371_);
v_snd_1372_ = lean_ctor_get(v_a_1370_, 1);
lean_inc(v_snd_1372_);
lean_dec(v_a_1370_);
v___x_1373_ = lean_expr_instantiate_rev(v_value_1365_, v_fvars_1354_);
lean_dec_ref(v_value_1365_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v_a_1356_);
lean_inc_ref(v_post_1350_);
lean_inc_ref(v_pre_1349_);
v___x_1374_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1349_, v_post_1350_, v_usedLetOnly_1351_, v_skipConstInApp_1352_, v_skipInstances_1353_, v___x_1373_, v_a_1356_, v_snd_1372_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v_fst_1376_; lean_object* v_snd_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___f_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref(v___x_1374_);
v_fst_1376_ = lean_ctor_get(v_a_1375_, 0);
lean_inc(v_fst_1376_);
v_snd_1377_ = lean_ctor_get(v_a_1375_, 1);
lean_inc(v_snd_1377_);
lean_dec(v_a_1375_);
v___x_1378_ = lean_box(v_usedLetOnly_1351_);
v___x_1379_ = lean_box(v_skipConstInApp_1352_);
v___x_1380_ = lean_box(v_skipInstances_1353_);
v___f_1381_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1381_, 0, v_fvars_1354_);
lean_closure_set(v___f_1381_, 1, v_pre_1349_);
lean_closure_set(v___f_1381_, 2, v_post_1350_);
lean_closure_set(v___f_1381_, 3, v___x_1378_);
lean_closure_set(v___f_1381_, 4, v___x_1379_);
lean_closure_set(v___f_1381_, 5, v___x_1380_);
lean_closure_set(v___f_1381_, 6, v_body_1366_);
v___x_1382_ = 0;
v___x_1383_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___redArg(v_declName_1363_, v_fst_1371_, v_fst_1376_, v___f_1381_, v_nondep_1367_, v___x_1382_, v_a_1356_, v_snd_1377_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1383_;
}
else
{
lean_dec(v_fst_1371_);
lean_dec_ref(v_body_1366_);
lean_dec(v_declName_1363_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v_a_1356_);
lean_dec_ref(v_fvars_1354_);
lean_dec_ref(v_post_1350_);
lean_dec_ref(v_pre_1349_);
return v___x_1374_;
}
}
else
{
lean_dec_ref(v_body_1366_);
lean_dec_ref(v_value_1365_);
lean_dec(v_declName_1363_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v_a_1356_);
lean_dec_ref(v_fvars_1354_);
lean_dec_ref(v_post_1350_);
lean_dec_ref(v_pre_1349_);
return v___x_1369_;
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_expr_instantiate_rev(v_e_1355_, v_fvars_1354_);
lean_dec_ref(v_e_1355_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v_a_1356_);
lean_inc_ref(v_post_1350_);
lean_inc_ref(v_pre_1349_);
v___x_1385_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1349_, v_post_1350_, v_usedLetOnly_1351_, v_skipConstInApp_1352_, v_skipInstances_1353_, v___x_1384_, v_a_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v_fst_1387_; lean_object* v_snd_1388_; uint8_t v___x_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref(v___x_1385_);
v_fst_1387_ = lean_ctor_get(v_a_1386_, 0);
lean_inc(v_fst_1387_);
v_snd_1388_ = lean_ctor_get(v_a_1386_, 1);
lean_inc(v_snd_1388_);
lean_dec(v_a_1386_);
v___x_1389_ = 0;
v___x_1390_ = 1;
v___x_1391_ = l_Lean_Meta_mkLetFVars(v_fvars_1354_, v_fst_1387_, v_usedLetOnly_1351_, v___x_1389_, v___x_1390_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec_ref(v_fvars_1354_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1349_, v_post_1350_, v_usedLetOnly_1351_, v_skipConstInApp_1352_, v_skipInstances_1353_, v_a_1392_, v_a_1356_, v_snd_1388_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1393_;
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_snd_1388_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v_a_1356_);
lean_dec_ref(v_post_1350_);
lean_dec_ref(v_pre_1349_);
v_a_1394_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1391_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1391_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v_a_1356_);
lean_dec_ref(v_fvars_1354_);
lean_dec_ref(v_post_1350_);
lean_dec_ref(v_pre_1349_);
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1402_, lean_object* v_post_1403_, uint8_t v_usedLetOnly_1404_, uint8_t v_skipConstInApp_1405_, uint8_t v_skipInstances_1406_, size_t v_sz_1407_, size_t v_i_1408_, lean_object* v_bs_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_usize_dec_lt(v_i_1408_, v_sz_1407_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1410_);
lean_dec_ref(v_post_1403_);
lean_dec_ref(v_pre_1402_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_bs_1409_);
lean_ctor_set(v___x_1418_, 1, v___y_1411_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
else
{
lean_object* v_v_1420_; lean_object* v___x_1421_; 
v_v_1420_ = lean_array_uget_borrowed(v_bs_1409_, v_i_1408_);
lean_inc(v___y_1415_);
lean_inc_ref(v___y_1414_);
lean_inc(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc(v___y_1410_);
lean_inc(v_v_1420_);
lean_inc_ref(v_post_1403_);
lean_inc_ref(v_pre_1402_);
v___x_1421_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1402_, v_post_1403_, v_usedLetOnly_1404_, v_skipConstInApp_1405_, v_skipInstances_1406_, v_v_1420_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v_fst_1423_; lean_object* v_snd_1424_; lean_object* v___x_1425_; lean_object* v_bs_x27_1426_; size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1421_);
v_fst_1423_ = lean_ctor_get(v_a_1422_, 0);
lean_inc(v_fst_1423_);
v_snd_1424_ = lean_ctor_get(v_a_1422_, 1);
lean_inc(v_snd_1424_);
lean_dec(v_a_1422_);
v___x_1425_ = lean_unsigned_to_nat(0u);
v_bs_x27_1426_ = lean_array_uset(v_bs_1409_, v_i_1408_, v___x_1425_);
v___x_1427_ = ((size_t)1ULL);
v___x_1428_ = lean_usize_add(v_i_1408_, v___x_1427_);
v___x_1429_ = lean_array_uset(v_bs_x27_1426_, v_i_1408_, v_fst_1423_);
v_i_1408_ = v___x_1428_;
v_bs_1409_ = v___x_1429_;
v___y_1411_ = v_snd_1424_;
goto _start;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1410_);
lean_dec_ref(v_bs_1409_);
lean_dec_ref(v_post_1403_);
lean_dec_ref(v_pre_1402_);
v_a_1431_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1421_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1421_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(lean_object* v_pre_1439_, lean_object* v_post_1440_, uint8_t v_usedLetOnly_1441_, uint8_t v_skipConstInApp_1442_, uint8_t v_skipInstances_1443_, lean_object* v___x_1444_, lean_object* v___y_1445_, lean_object* v_b_1446_, lean_object* v_a_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1439_, v_post_1440_, v_usedLetOnly_1441_, v_skipConstInApp_1442_, v_skipInstances_1443_, v___x_1444_, v___y_1445_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1473_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1473_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1473_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_fst_1459_; lean_object* v_snd_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1472_; 
v_fst_1459_ = lean_ctor_get(v_a_1455_, 0);
v_snd_1460_ = lean_ctor_get(v_a_1455_, 1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_a_1455_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1462_ = v_a_1455_;
v_isShared_1463_ = v_isSharedCheck_1472_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_snd_1460_);
lean_inc(v_fst_1459_);
lean_dec(v_a_1455_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1472_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1464_ = lean_array_fset(v_b_1446_, v_a_1447_, v_fst_1459_);
v___x_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1465_);
v___x_1467_ = v___x_1462_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_snd_1460_);
v___x_1467_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1467_);
v___x_1469_ = v___x_1457_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec_ref(v_b_1446_);
v_a_1474_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1454_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1454_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed(lean_object* v_pre_1482_, lean_object* v_post_1483_, lean_object* v_usedLetOnly_1484_, lean_object* v_skipConstInApp_1485_, lean_object* v_skipInstances_1486_, lean_object* v___x_1487_, lean_object* v___y_1488_, lean_object* v_b_1489_, lean_object* v_a_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v_usedLetOnly_boxed_1497_; uint8_t v_skipConstInApp_boxed_1498_; uint8_t v_skipInstances_boxed_1499_; lean_object* v_res_1500_; 
v_usedLetOnly_boxed_1497_ = lean_unbox(v_usedLetOnly_1484_);
v_skipConstInApp_boxed_1498_ = lean_unbox(v_skipConstInApp_1485_);
v_skipInstances_boxed_1499_ = lean_unbox(v_skipInstances_1486_);
v_res_1500_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(v_pre_1482_, v_post_1483_, v_usedLetOnly_boxed_1497_, v_skipConstInApp_boxed_1498_, v_skipInstances_boxed_1499_, v___x_1487_, v___y_1488_, v_b_1489_, v_a_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v_a_1490_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_1501_, lean_object* v___x_1502_, lean_object* v_pre_1503_, lean_object* v_post_1504_, uint8_t v_usedLetOnly_1505_, uint8_t v_skipConstInApp_1506_, uint8_t v_skipInstances_1507_, lean_object* v_a_1508_, lean_object* v_b_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___y_1518_; uint8_t v___x_1552_; 
v___x_1552_ = lean_nat_dec_lt(v_a_1508_, v_upperBound_1501_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1510_);
lean_dec(v_a_1508_);
lean_dec_ref(v_post_1504_);
lean_dec_ref(v_pre_1503_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_b_1509_);
lean_ctor_set(v___x_1553_, 1, v___y_1511_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = lean_array_fget_borrowed(v_b_1509_, v_a_1508_);
v___x_1556_ = lean_array_get_size(v___x_1502_);
v___x_1557_ = lean_nat_dec_lt(v_a_1508_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___f_1561_; 
lean_inc(v___x_1555_);
v___x_1558_ = lean_box(v_usedLetOnly_1505_);
v___x_1559_ = lean_box(v_skipConstInApp_1506_);
v___x_1560_ = lean_box(v_skipInstances_1507_);
lean_inc(v_a_1508_);
lean_inc(v___y_1510_);
lean_inc_ref(v_post_1504_);
lean_inc_ref(v_pre_1503_);
v___f_1561_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1561_, 0, v_pre_1503_);
lean_closure_set(v___f_1561_, 1, v_post_1504_);
lean_closure_set(v___f_1561_, 2, v___x_1558_);
lean_closure_set(v___f_1561_, 3, v___x_1559_);
lean_closure_set(v___f_1561_, 4, v___x_1560_);
lean_closure_set(v___f_1561_, 5, v___x_1555_);
lean_closure_set(v___f_1561_, 6, v___y_1510_);
lean_closure_set(v___f_1561_, 7, v_b_1509_);
lean_closure_set(v___f_1561_, 8, v_a_1508_);
v___y_1518_ = v___f_1561_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1562_; uint8_t v_isInstance_1563_; 
v___x_1562_ = lean_array_fget_borrowed(v___x_1502_, v_a_1508_);
v_isInstance_1563_ = lean_ctor_get_uint8(v___x_1562_, sizeof(void*)*1 + 4);
if (v_isInstance_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___f_1567_; 
lean_inc(v___x_1555_);
v___x_1564_ = lean_box(v_usedLetOnly_1505_);
v___x_1565_ = lean_box(v_skipConstInApp_1506_);
v___x_1566_ = lean_box(v_skipInstances_1507_);
lean_inc(v_a_1508_);
lean_inc(v___y_1510_);
lean_inc_ref(v_post_1504_);
lean_inc_ref(v_pre_1503_);
v___f_1567_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1567_, 0, v_pre_1503_);
lean_closure_set(v___f_1567_, 1, v_post_1504_);
lean_closure_set(v___f_1567_, 2, v___x_1564_);
lean_closure_set(v___f_1567_, 3, v___x_1565_);
lean_closure_set(v___f_1567_, 4, v___x_1566_);
lean_closure_set(v___f_1567_, 5, v___x_1555_);
lean_closure_set(v___f_1567_, 6, v___y_1510_);
lean_closure_set(v___f_1567_, 7, v_b_1509_);
lean_closure_set(v___f_1567_, 8, v_a_1508_);
v___y_1518_ = v___f_1567_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1568_; lean_object* v___f_1569_; 
v___x_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_b_1509_);
v___f_1569_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1569_, 0, v___x_1568_);
v___y_1518_ = v___f_1569_;
goto v___jp_1517_;
}
}
}
v___jp_1517_:
{
lean_object* v___x_1519_; 
lean_inc(v___y_1515_);
lean_inc_ref(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc_ref(v___y_1512_);
v___x_1519_ = lean_apply_6(v___y_1518_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, lean_box(0));
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1543_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1543_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1543_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_fst_1524_; 
v_fst_1524_ = lean_ctor_get(v_a_1520_, 0);
lean_inc(v_fst_1524_);
if (lean_obj_tag(v_fst_1524_) == 0)
{
lean_object* v_snd_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1510_);
lean_dec(v_a_1508_);
lean_dec_ref(v_post_1504_);
lean_dec_ref(v_pre_1503_);
v_snd_1525_ = lean_ctor_get(v_a_1520_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_a_1520_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_a_1520_, 0);
lean_dec(v_unused_1537_);
v___x_1527_ = v_a_1520_;
v_isShared_1528_ = v_isSharedCheck_1536_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_snd_1525_);
lean_dec(v_a_1520_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1536_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_a_1529_; lean_object* v___x_1531_; 
v_a_1529_ = lean_ctor_get(v_fst_1524_, 0);
lean_inc(v_a_1529_);
lean_dec_ref(v_fst_1524_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_a_1529_);
v___x_1531_ = v___x_1527_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_snd_1525_);
v___x_1531_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1531_);
v___x_1533_ = v___x_1522_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_snd_1538_; lean_object* v_a_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_del_object(v___x_1522_);
v_snd_1538_ = lean_ctor_get(v_a_1520_, 1);
lean_inc(v_snd_1538_);
lean_dec(v_a_1520_);
v_a_1539_ = lean_ctor_get(v_fst_1524_, 0);
lean_inc(v_a_1539_);
lean_dec_ref(v_fst_1524_);
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = lean_nat_add(v_a_1508_, v___x_1540_);
lean_dec(v_a_1508_);
v_a_1508_ = v___x_1541_;
v_b_1509_ = v_a_1539_;
v___y_1511_ = v_snd_1538_;
goto _start;
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1510_);
lean_dec(v_a_1508_);
lean_dec_ref(v_post_1504_);
lean_dec_ref(v_pre_1503_);
v_a_1544_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1519_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1519_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(uint8_t v_skipInstances_1570_, lean_object* v_pre_1571_, lean_object* v_post_1572_, uint8_t v_usedLetOnly_1573_, uint8_t v_skipConstInApp_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_f_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; 
if (lean_obj_tag(v_x_1575_) == 5)
{
lean_object* v_fn_1641_; lean_object* v_arg_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_fn_1641_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_fn_1641_);
v_arg_1642_ = lean_ctor_get(v_x_1575_, 1);
lean_inc_ref(v_arg_1642_);
lean_dec_ref(v_x_1575_);
v___x_1643_ = lean_array_set(v_x_1576_, v_x_1577_, v_arg_1642_);
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_nat_sub(v_x_1577_, v___x_1644_);
lean_dec(v_x_1577_);
v_x_1575_ = v_fn_1641_;
v_x_1576_ = v___x_1643_;
v_x_1577_ = v___x_1645_;
goto _start;
}
else
{
lean_dec(v_x_1577_);
if (v_skipConstInApp_1574_ == 0)
{
goto v___jp_1636_;
}
else
{
uint8_t v___x_1647_; 
v___x_1647_ = l_Lean_Expr_isConst(v_x_1575_);
if (v___x_1647_ == 0)
{
goto v___jp_1636_;
}
else
{
v_f_1586_ = v_x_1575_;
v___y_1587_ = v___y_1578_;
v___y_1588_ = v___y_1579_;
v___y_1589_ = v___y_1580_;
v___y_1590_ = v___y_1581_;
v___y_1591_ = v___y_1582_;
v___y_1592_ = v___y_1583_;
goto v___jp_1585_;
}
}
}
v___jp_1585_:
{
if (v_skipInstances_1570_ == 0)
{
size_t v_sz_1593_; size_t v___x_1594_; lean_object* v___x_1595_; 
v_sz_1593_ = lean_array_size(v_x_1576_);
v___x_1594_ = ((size_t)0ULL);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1587_);
lean_inc_ref(v_post_1572_);
lean_inc_ref(v_pre_1571_);
v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1571_, v_post_1572_, v_usedLetOnly_1573_, v_skipConstInApp_1574_, v_skipInstances_1570_, v_sz_1593_, v___x_1594_, v_x_1576_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v_fst_1597_; lean_object* v_snd_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
v_fst_1597_ = lean_ctor_get(v_a_1596_, 0);
lean_inc(v_fst_1597_);
v_snd_1598_ = lean_ctor_get(v_a_1596_, 1);
lean_inc(v_snd_1598_);
lean_dec(v_a_1596_);
v___x_1599_ = l_Lean_mkAppN(v_f_1586_, v_fst_1597_);
lean_dec(v_fst_1597_);
v___x_1600_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1571_, v_post_1572_, v_usedLetOnly_1573_, v_skipConstInApp_1574_, v_skipInstances_1570_, v___x_1599_, v___y_1587_, v_snd_1598_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
return v___x_1600_;
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1587_);
lean_dec_ref(v_f_1586_);
lean_dec_ref(v_post_1572_);
lean_dec_ref(v_pre_1571_);
v_a_1601_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1595_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1595_);
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
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_array_get_size(v_x_1576_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc_ref(v_f_1586_);
v___x_1610_ = l_Lean_Meta_getFunInfoNArgs(v_f_1586_, v___x_1609_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v_paramInfo_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v___x_1610_);
v_paramInfo_1612_ = lean_ctor_get(v_a_1611_, 0);
lean_inc_ref(v_paramInfo_1612_);
lean_dec(v_a_1611_);
v___x_1613_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1587_);
lean_inc_ref(v_post_1572_);
lean_inc_ref(v_pre_1571_);
v___x_1614_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v___x_1609_, v_paramInfo_1612_, v_pre_1571_, v_post_1572_, v_usedLetOnly_1573_, v_skipConstInApp_1574_, v_skipInstances_1570_, v___x_1613_, v_x_1576_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec_ref(v_paramInfo_1612_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v_fst_1616_; lean_object* v_snd_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1614_);
v_fst_1616_ = lean_ctor_get(v_a_1615_, 0);
lean_inc(v_fst_1616_);
v_snd_1617_ = lean_ctor_get(v_a_1615_, 1);
lean_inc(v_snd_1617_);
lean_dec(v_a_1615_);
v___x_1618_ = l_Lean_mkAppN(v_f_1586_, v_fst_1616_);
lean_dec(v_fst_1616_);
v___x_1619_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1571_, v_post_1572_, v_usedLetOnly_1573_, v_skipConstInApp_1574_, v_skipInstances_1570_, v___x_1618_, v___y_1587_, v_snd_1617_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
return v___x_1619_;
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1587_);
lean_dec_ref(v_f_1586_);
lean_dec_ref(v_post_1572_);
lean_dec_ref(v_pre_1571_);
v_a_1620_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1614_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1614_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v_f_1586_);
lean_dec_ref(v_x_1576_);
lean_dec_ref(v_post_1572_);
lean_dec_ref(v_pre_1571_);
v_a_1628_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1610_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1610_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
v___jp_1636_:
{
lean_object* v___x_1637_; 
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1580_);
lean_inc(v___y_1578_);
lean_inc_ref(v_post_1572_);
lean_inc_ref(v_pre_1571_);
v___x_1637_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1571_, v_post_1572_, v_usedLetOnly_1573_, v_skipConstInApp_1574_, v_skipInstances_1570_, v_x_1575_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v_fst_1639_; lean_object* v_snd_1640_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref(v___x_1637_);
v_fst_1639_ = lean_ctor_get(v_a_1638_, 0);
lean_inc(v_fst_1639_);
v_snd_1640_ = lean_ctor_get(v_a_1638_, 1);
lean_inc(v_snd_1640_);
lean_dec(v_a_1638_);
v_f_1586_ = v_fst_1639_;
v___y_1587_ = v___y_1578_;
v___y_1588_ = v_snd_1640_;
v___y_1589_ = v___y_1580_;
v___y_1590_ = v___y_1581_;
v___y_1591_ = v___y_1582_;
v___y_1592_ = v___y_1583_;
goto v___jp_1585_;
}
else
{
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1578_);
lean_dec_ref(v_x_1576_);
lean_dec_ref(v_post_1572_);
lean_dec_ref(v_pre_1571_);
return v___x_1637_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v_pre_1648_, lean_object* v_e_1649_, lean_object* v_post_1650_, uint8_t v_usedLetOnly_1651_, uint8_t v_skipConstInApp_1652_, uint8_t v_skipInstances_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; 
lean_inc_ref(v_pre_1648_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc_ref(v_e_1649_);
v___x_1661_ = lean_apply_7(v_pre_1648_, v_e_1649_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, lean_box(0));
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1723_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1723_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1723_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_fst_1666_; lean_object* v_snd_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1722_; 
v_fst_1666_ = lean_ctor_get(v_a_1662_, 0);
v_snd_1667_ = lean_ctor_get(v_a_1662_, 1);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_a_1662_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1669_ = v_a_1662_;
v_isShared_1670_ = v_isSharedCheck_1722_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_snd_1667_);
lean_inc(v_fst_1666_);
lean_dec(v_a_1662_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1722_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___y_1672_; 
switch(lean_obj_tag(v_fst_1666_))
{
case 0:
{
lean_object* v_e_1711_; lean_object* v___x_1713_; 
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1654_);
lean_dec_ref(v_post_1650_);
lean_dec_ref(v_e_1649_);
lean_dec_ref(v_pre_1648_);
v_e_1711_ = lean_ctor_get(v_fst_1666_, 0);
lean_inc_ref(v_e_1711_);
lean_dec_ref(v_fst_1666_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_e_1711_);
v___x_1713_ = v___x_1669_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_e_1711_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_snd_1667_);
v___x_1713_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1715_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1713_);
v___x_1715_ = v___x_1664_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
case 1:
{
lean_object* v_e_1718_; lean_object* v___x_1719_; 
lean_del_object(v___x_1669_);
lean_del_object(v___x_1664_);
lean_dec_ref(v_e_1649_);
v_e_1718_ = lean_ctor_get(v_fst_1666_, 0);
lean_inc_ref(v_e_1718_);
lean_dec_ref(v_fst_1666_);
v___x_1719_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v_e_1718_, v___y_1654_, v_snd_1667_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1719_;
}
default: 
{
lean_object* v_e_x3f_1720_; 
lean_del_object(v___x_1669_);
lean_del_object(v___x_1664_);
v_e_x3f_1720_ = lean_ctor_get(v_fst_1666_, 0);
lean_inc(v_e_x3f_1720_);
lean_dec_ref(v_fst_1666_);
if (lean_obj_tag(v_e_x3f_1720_) == 0)
{
v___y_1672_ = v_e_1649_;
goto v___jp_1671_;
}
else
{
lean_object* v_val_1721_; 
lean_dec_ref(v_e_1649_);
v_val_1721_ = lean_ctor_get(v_e_x3f_1720_, 0);
lean_inc(v_val_1721_);
lean_dec_ref(v_e_x3f_1720_);
v___y_1672_ = v_val_1721_;
goto v___jp_1671_;
}
}
}
v___jp_1671_:
{
switch(lean_obj_tag(v___y_1672_))
{
case 7:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1674_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v___x_1673_, v___y_1672_, v___y_1654_, v_snd_1667_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1674_;
}
case 6:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1676_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v___x_1675_, v___y_1672_, v___y_1654_, v_snd_1667_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1676_;
}
case 8:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v___x_1677_, v___y_1672_, v___y_1654_, v_snd_1667_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1678_;
}
case 5:
{
lean_object* v_dummy_1679_; lean_object* v_nargs_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_dummy_1679_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1680_ = l_Lean_Expr_getAppNumArgs(v___y_1672_);
lean_inc(v_nargs_1680_);
v___x_1681_ = lean_mk_array(v_nargs_1680_, v_dummy_1679_);
v___x_1682_ = lean_unsigned_to_nat(1u);
v___x_1683_ = lean_nat_sub(v_nargs_1680_, v___x_1682_);
lean_dec(v_nargs_1680_);
v___x_1684_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_skipInstances_1653_, v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v___y_1672_, v___x_1681_, v___x_1683_, v___y_1654_, v_snd_1667_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1684_;
}
case 10:
{
lean_object* v_data_1685_; lean_object* v_expr_1686_; lean_object* v___x_1687_; 
v_data_1685_ = lean_ctor_get(v___y_1672_, 0);
v_expr_1686_ = lean_ctor_get(v___y_1672_, 1);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1654_);
lean_inc_ref(v_expr_1686_);
lean_inc_ref(v_post_1650_);
lean_inc_ref(v_pre_1648_);
v___x_1687_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v_expr_1686_, v___y_1654_, v_snd_1667_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v_fst_1689_; lean_object* v_snd_1690_; size_t v___x_1691_; size_t v___x_1692_; uint8_t v___x_1693_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1687_);
v_fst_1689_ = lean_ctor_get(v_a_1688_, 0);
lean_inc(v_fst_1689_);
v_snd_1690_ = lean_ctor_get(v_a_1688_, 1);
lean_inc(v_snd_1690_);
lean_dec(v_a_1688_);
v___x_1691_ = lean_ptr_addr(v_expr_1686_);
v___x_1692_ = lean_ptr_addr(v_fst_1689_);
v___x_1693_ = lean_usize_dec_eq(v___x_1691_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc(v_data_1685_);
lean_dec_ref(v___y_1672_);
v___x_1694_ = l_Lean_Expr_mdata___override(v_data_1685_, v_fst_1689_);
v___x_1695_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v___x_1694_, v___y_1654_, v_snd_1690_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1695_;
}
else
{
lean_object* v___x_1696_; 
lean_dec(v_fst_1689_);
v___x_1696_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v___y_1672_, v___y_1654_, v_snd_1690_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1696_;
}
}
else
{
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1654_);
lean_dec_ref(v_post_1650_);
lean_dec_ref(v_pre_1648_);
return v___x_1687_;
}
}
case 11:
{
lean_object* v_typeName_1697_; lean_object* v_idx_1698_; lean_object* v_struct_1699_; lean_object* v___x_1700_; 
v_typeName_1697_ = lean_ctor_get(v___y_1672_, 0);
v_idx_1698_ = lean_ctor_get(v___y_1672_, 1);
v_struct_1699_ = lean_ctor_get(v___y_1672_, 2);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1654_);
lean_inc_ref(v_struct_1699_);
lean_inc_ref(v_post_1650_);
lean_inc_ref(v_pre_1648_);
v___x_1700_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v_struct_1699_, v___y_1654_, v_snd_1667_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v_fst_1702_; lean_object* v_snd_1703_; size_t v___x_1704_; size_t v___x_1705_; uint8_t v___x_1706_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref(v___x_1700_);
v_fst_1702_ = lean_ctor_get(v_a_1701_, 0);
lean_inc(v_fst_1702_);
v_snd_1703_ = lean_ctor_get(v_a_1701_, 1);
lean_inc(v_snd_1703_);
lean_dec(v_a_1701_);
v___x_1704_ = lean_ptr_addr(v_struct_1699_);
v___x_1705_ = lean_ptr_addr(v_fst_1702_);
v___x_1706_ = lean_usize_dec_eq(v___x_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_inc(v_idx_1698_);
lean_inc(v_typeName_1697_);
lean_dec_ref(v___y_1672_);
v___x_1707_ = l_Lean_Expr_proj___override(v_typeName_1697_, v_idx_1698_, v_fst_1702_);
v___x_1708_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v___x_1707_, v___y_1654_, v_snd_1703_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1708_;
}
else
{
lean_object* v___x_1709_; 
lean_dec(v_fst_1702_);
v___x_1709_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v___y_1672_, v___y_1654_, v_snd_1703_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1709_;
}
}
else
{
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1654_);
lean_dec_ref(v_post_1650_);
lean_dec_ref(v_pre_1648_);
return v___x_1700_;
}
}
default: 
{
lean_object* v___x_1710_; 
v___x_1710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1648_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v___y_1672_, v___y_1654_, v_snd_1667_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1710_;
}
}
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1654_);
lean_dec_ref(v_post_1650_);
lean_dec_ref(v_e_1649_);
lean_dec_ref(v_pre_1648_);
v_a_1724_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1661_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1661_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v_pre_1732_, lean_object* v_e_1733_, lean_object* v_post_1734_, lean_object* v_usedLetOnly_1735_, lean_object* v_skipConstInApp_1736_, lean_object* v_skipInstances_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v_usedLetOnly_boxed_1745_; uint8_t v_skipConstInApp_boxed_1746_; uint8_t v_skipInstances_boxed_1747_; lean_object* v_res_1748_; 
v_usedLetOnly_boxed_1745_ = lean_unbox(v_usedLetOnly_1735_);
v_skipConstInApp_boxed_1746_ = lean_unbox(v_skipConstInApp_1736_);
v_skipInstances_boxed_1747_ = lean_unbox(v_skipInstances_1737_);
v_res_1748_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v_pre_1732_, v_e_1733_, v_post_1734_, v_usedLetOnly_boxed_1745_, v_skipConstInApp_boxed_1746_, v_skipInstances_boxed_1747_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1749_, lean_object* v_post_1750_, uint8_t v_usedLetOnly_1751_, uint8_t v_skipConstInApp_1752_, uint8_t v_skipInstances_1753_, lean_object* v_e_1754_, lean_object* v_a_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_inc(v_a_1755_);
v___x_1762_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1762_, 0, lean_box(0));
lean_closure_set(v___x_1762_, 1, lean_box(0));
lean_closure_set(v___x_1762_, 2, v_a_1755_);
v___x_1763_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1762_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1817_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1817_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1817_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v_fst_1768_; lean_object* v_snd_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1816_; 
v_fst_1768_ = lean_ctor_get(v_a_1764_, 0);
v_snd_1769_ = lean_ctor_get(v_a_1764_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_a_1764_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1771_ = v_a_1764_;
v_isShared_1772_ = v_isSharedCheck_1816_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_snd_1769_);
lean_inc(v_fst_1768_);
lean_dec(v_a_1764_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1816_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_fst_1768_, v_e_1754_);
lean_dec(v_fst_1768_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___f_1777_; lean_object* v___x_1778_; 
lean_del_object(v___x_1771_);
lean_del_object(v___x_1766_);
v___x_1774_ = lean_box(v_usedLetOnly_1751_);
v___x_1775_ = lean_box(v_skipConstInApp_1752_);
v___x_1776_ = lean_box(v_skipInstances_1753_);
lean_inc_ref(v_e_1754_);
v___f_1777_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1777_, 0, v_pre_1749_);
lean_closure_set(v___f_1777_, 1, v_e_1754_);
lean_closure_set(v___f_1777_, 2, v_post_1750_);
lean_closure_set(v___f_1777_, 3, v___x_1774_);
lean_closure_set(v___f_1777_, 4, v___x_1775_);
lean_closure_set(v___f_1777_, 5, v___x_1776_);
lean_inc(v___y_1760_);
lean_inc_ref(v___y_1759_);
lean_inc(v___y_1758_);
lean_inc_ref(v___y_1757_);
lean_inc(v_a_1755_);
v___x_1778_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___f_1777_, v_a_1755_, v_snd_1769_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v_fst_1780_; lean_object* v_snd_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1778_);
v_fst_1780_ = lean_ctor_get(v_a_1779_, 0);
lean_inc(v_fst_1780_);
v_snd_1781_ = lean_ctor_get(v_a_1779_, 1);
lean_inc(v_snd_1781_);
lean_dec(v_a_1779_);
lean_inc(v_fst_1780_);
v___f_1782_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1782_, 0, v_a_1755_);
lean_closure_set(v___f_1782_, 1, v_e_1754_);
lean_closure_set(v___f_1782_, 2, v_fst_1780_);
v___x_1783_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1782_, v_snd_1781_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1800_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1800_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1800_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v_snd_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1798_; 
v_snd_1788_ = lean_ctor_get(v_a_1784_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_a_1784_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v_a_1784_, 0);
lean_dec(v_unused_1799_);
v___x_1790_ = v_a_1784_;
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_snd_1788_);
lean_dec(v_a_1784_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v_fst_1780_);
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_fst_1780_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_snd_1788_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1793_);
v___x_1795_ = v___x_1786_;
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
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v_fst_1780_);
v_a_1801_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1783_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1783_);
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
else
{
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v_a_1755_);
lean_dec_ref(v_e_1754_);
return v___x_1778_;
}
}
else
{
lean_object* v_val_1809_; lean_object* v___x_1811_; 
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v_a_1755_);
lean_dec_ref(v_e_1754_);
lean_dec_ref(v_post_1750_);
lean_dec_ref(v_pre_1749_);
v_val_1809_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_val_1809_);
lean_dec_ref(v___x_1773_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v_val_1809_);
v___x_1811_ = v___x_1771_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_val_1809_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_snd_1769_);
v___x_1811_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1811_);
v___x_1813_ = v___x_1766_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v_a_1755_);
lean_dec_ref(v_e_1754_);
lean_dec_ref(v_post_1750_);
lean_dec_ref(v_pre_1749_);
v_a_1818_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1763_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1763_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1826_, lean_object* v_pre_1827_, lean_object* v_post_1828_, lean_object* v_usedLetOnly_1829_, lean_object* v_skipConstInApp_1830_, lean_object* v_skipInstances_1831_, lean_object* v_body_1832_, lean_object* v_x_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v_usedLetOnly_boxed_1841_; uint8_t v_skipConstInApp_boxed_1842_; uint8_t v_skipInstances_boxed_1843_; lean_object* v_res_1844_; 
v_usedLetOnly_boxed_1841_ = lean_unbox(v_usedLetOnly_1829_);
v_skipConstInApp_boxed_1842_ = lean_unbox(v_skipConstInApp_1830_);
v_skipInstances_boxed_1843_ = lean_unbox(v_skipInstances_1831_);
v_res_1844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1826_, v_pre_1827_, v_post_1828_, v_usedLetOnly_boxed_1841_, v_skipConstInApp_boxed_1842_, v_skipInstances_boxed_1843_, v_body_1832_, v_x_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1845_, lean_object* v_post_1846_, uint8_t v_usedLetOnly_1847_, uint8_t v_skipConstInApp_1848_, uint8_t v_skipInstances_1849_, lean_object* v_fvars_1850_, lean_object* v_e_1851_, lean_object* v_a_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
if (lean_obj_tag(v_e_1851_) == 7)
{
lean_object* v_binderName_1859_; lean_object* v_binderType_1860_; lean_object* v_body_1861_; uint8_t v_binderInfo_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_binderName_1859_ = lean_ctor_get(v_e_1851_, 0);
lean_inc(v_binderName_1859_);
v_binderType_1860_ = lean_ctor_get(v_e_1851_, 1);
lean_inc_ref(v_binderType_1860_);
v_body_1861_ = lean_ctor_get(v_e_1851_, 2);
lean_inc_ref(v_body_1861_);
v_binderInfo_1862_ = lean_ctor_get_uint8(v_e_1851_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1851_);
v___x_1863_ = lean_expr_instantiate_rev(v_binderType_1860_, v_fvars_1850_);
lean_dec_ref(v_binderType_1860_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc(v_a_1852_);
lean_inc_ref(v_post_1846_);
lean_inc_ref(v_pre_1845_);
v___x_1864_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1845_, v_post_1846_, v_usedLetOnly_1847_, v_skipConstInApp_1848_, v_skipInstances_1849_, v___x_1863_, v_a_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v_fst_1866_; lean_object* v_snd_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___f_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
v_fst_1866_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_fst_1866_);
v_snd_1867_ = lean_ctor_get(v_a_1865_, 1);
lean_inc(v_snd_1867_);
lean_dec(v_a_1865_);
v___x_1868_ = lean_box(v_usedLetOnly_1847_);
v___x_1869_ = lean_box(v_skipConstInApp_1848_);
v___x_1870_ = lean_box(v_skipInstances_1849_);
v___f_1871_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1871_, 0, v_fvars_1850_);
lean_closure_set(v___f_1871_, 1, v_pre_1845_);
lean_closure_set(v___f_1871_, 2, v_post_1846_);
lean_closure_set(v___f_1871_, 3, v___x_1868_);
lean_closure_set(v___f_1871_, 4, v___x_1869_);
lean_closure_set(v___f_1871_, 5, v___x_1870_);
lean_closure_set(v___f_1871_, 6, v_body_1861_);
v___x_1872_ = 0;
v___x_1873_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg(v_binderName_1859_, v_binderInfo_1862_, v_fst_1866_, v___f_1871_, v___x_1872_, v_a_1852_, v_snd_1867_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
return v___x_1873_;
}
else
{
lean_dec_ref(v_body_1861_);
lean_dec(v_binderName_1859_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_a_1852_);
lean_dec_ref(v_fvars_1850_);
lean_dec_ref(v_post_1846_);
lean_dec_ref(v_pre_1845_);
return v___x_1864_;
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_expr_instantiate_rev(v_e_1851_, v_fvars_1850_);
lean_dec_ref(v_e_1851_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc(v_a_1852_);
lean_inc_ref(v_post_1846_);
lean_inc_ref(v_pre_1845_);
v___x_1875_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1845_, v_post_1846_, v_usedLetOnly_1847_, v_skipConstInApp_1848_, v_skipInstances_1849_, v___x_1874_, v_a_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v_fst_1877_; lean_object* v_snd_1878_; uint8_t v___x_1879_; uint8_t v___x_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref(v___x_1875_);
v_fst_1877_ = lean_ctor_get(v_a_1876_, 0);
lean_inc(v_fst_1877_);
v_snd_1878_ = lean_ctor_get(v_a_1876_, 1);
lean_inc(v_snd_1878_);
lean_dec(v_a_1876_);
v___x_1879_ = 0;
v___x_1880_ = 1;
v___x_1881_ = 1;
v___x_1882_ = l_Lean_Meta_mkForallFVars(v_fvars_1850_, v_fst_1877_, v___x_1879_, v_usedLetOnly_1847_, v___x_1880_, v___x_1881_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec_ref(v_fvars_1850_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1845_, v_post_1846_, v_usedLetOnly_1847_, v_skipConstInApp_1848_, v_skipInstances_1849_, v_a_1883_, v_a_1852_, v_snd_1878_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
return v___x_1884_;
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_snd_1878_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_a_1852_);
lean_dec_ref(v_post_1846_);
lean_dec_ref(v_pre_1845_);
v_a_1885_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1882_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1882_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_a_1852_);
lean_dec_ref(v_fvars_1850_);
lean_dec_ref(v_post_1846_);
lean_dec_ref(v_pre_1845_);
return v___x_1875_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1893_, lean_object* v_pre_1894_, lean_object* v_post_1895_, uint8_t v_usedLetOnly_1896_, uint8_t v_skipConstInApp_1897_, uint8_t v_skipInstances_1898_, lean_object* v_body_1899_, lean_object* v_x_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_array_push(v_fvars_1893_, v_x_1900_);
v___x_1909_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1894_, v_post_1895_, v_usedLetOnly_1896_, v_skipConstInApp_1897_, v_skipInstances_1898_, v___x_1908_, v_body_1899_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1910_, lean_object* v_post_1911_, lean_object* v_usedLetOnly_1912_, lean_object* v_skipConstInApp_1913_, lean_object* v_skipInstances_1914_, lean_object* v_sz_1915_, lean_object* v_i_1916_, lean_object* v_bs_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
uint8_t v_usedLetOnly_boxed_1925_; uint8_t v_skipConstInApp_boxed_1926_; uint8_t v_skipInstances_boxed_1927_; size_t v_sz_boxed_1928_; size_t v_i_boxed_1929_; lean_object* v_res_1930_; 
v_usedLetOnly_boxed_1925_ = lean_unbox(v_usedLetOnly_1912_);
v_skipConstInApp_boxed_1926_ = lean_unbox(v_skipConstInApp_1913_);
v_skipInstances_boxed_1927_ = lean_unbox(v_skipInstances_1914_);
v_sz_boxed_1928_ = lean_unbox_usize(v_sz_1915_);
lean_dec(v_sz_1915_);
v_i_boxed_1929_ = lean_unbox_usize(v_i_1916_);
lean_dec(v_i_1916_);
v_res_1930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1910_, v_post_1911_, v_usedLetOnly_boxed_1925_, v_skipConstInApp_boxed_1926_, v_skipInstances_boxed_1927_, v_sz_boxed_1928_, v_i_boxed_1929_, v_bs_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object* v_pre_1931_, lean_object* v_post_1932_, lean_object* v_usedLetOnly_1933_, lean_object* v_skipConstInApp_1934_, lean_object* v_skipInstances_1935_, lean_object* v_e_1936_, lean_object* v_a_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
uint8_t v_usedLetOnly_boxed_1944_; uint8_t v_skipConstInApp_boxed_1945_; uint8_t v_skipInstances_boxed_1946_; lean_object* v_res_1947_; 
v_usedLetOnly_boxed_1944_ = lean_unbox(v_usedLetOnly_1933_);
v_skipConstInApp_boxed_1945_ = lean_unbox(v_skipConstInApp_1934_);
v_skipInstances_boxed_1946_ = lean_unbox(v_skipInstances_1935_);
v_res_1947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1931_, v_post_1932_, v_usedLetOnly_boxed_1944_, v_skipConstInApp_boxed_1945_, v_skipInstances_boxed_1946_, v_e_1936_, v_a_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1948_, lean_object* v_post_1949_, lean_object* v_usedLetOnly_1950_, lean_object* v_skipConstInApp_1951_, lean_object* v_skipInstances_1952_, lean_object* v_fvars_1953_, lean_object* v_e_1954_, lean_object* v_a_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
uint8_t v_usedLetOnly_boxed_1962_; uint8_t v_skipConstInApp_boxed_1963_; uint8_t v_skipInstances_boxed_1964_; lean_object* v_res_1965_; 
v_usedLetOnly_boxed_1962_ = lean_unbox(v_usedLetOnly_1950_);
v_skipConstInApp_boxed_1963_ = lean_unbox(v_skipConstInApp_1951_);
v_skipInstances_boxed_1964_ = lean_unbox(v_skipInstances_1952_);
v_res_1965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1948_, v_post_1949_, v_usedLetOnly_boxed_1962_, v_skipConstInApp_boxed_1963_, v_skipInstances_boxed_1964_, v_fvars_1953_, v_e_1954_, v_a_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1966_, lean_object* v_post_1967_, lean_object* v_usedLetOnly_1968_, lean_object* v_skipConstInApp_1969_, lean_object* v_skipInstances_1970_, lean_object* v_fvars_1971_, lean_object* v_e_1972_, lean_object* v_a_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
uint8_t v_usedLetOnly_boxed_1980_; uint8_t v_skipConstInApp_boxed_1981_; uint8_t v_skipInstances_boxed_1982_; lean_object* v_res_1983_; 
v_usedLetOnly_boxed_1980_ = lean_unbox(v_usedLetOnly_1968_);
v_skipConstInApp_boxed_1981_ = lean_unbox(v_skipConstInApp_1969_);
v_skipInstances_boxed_1982_ = lean_unbox(v_skipInstances_1970_);
v_res_1983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1966_, v_post_1967_, v_usedLetOnly_boxed_1980_, v_skipConstInApp_boxed_1981_, v_skipInstances_boxed_1982_, v_fvars_1971_, v_e_1972_, v_a_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1984_, lean_object* v_post_1985_, lean_object* v_usedLetOnly_1986_, lean_object* v_skipConstInApp_1987_, lean_object* v_skipInstances_1988_, lean_object* v_e_1989_, lean_object* v_a_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
uint8_t v_usedLetOnly_boxed_1997_; uint8_t v_skipConstInApp_boxed_1998_; uint8_t v_skipInstances_boxed_1999_; lean_object* v_res_2000_; 
v_usedLetOnly_boxed_1997_ = lean_unbox(v_usedLetOnly_1986_);
v_skipConstInApp_boxed_1998_ = lean_unbox(v_skipConstInApp_1987_);
v_skipInstances_boxed_1999_ = lean_unbox(v_skipInstances_1988_);
v_res_2000_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1984_, v_post_1985_, v_usedLetOnly_boxed_1997_, v_skipConstInApp_boxed_1998_, v_skipInstances_boxed_1999_, v_e_1989_, v_a_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_pre_2001_, lean_object* v_post_2002_, lean_object* v_usedLetOnly_2003_, lean_object* v_skipConstInApp_2004_, lean_object* v_skipInstances_2005_, lean_object* v_fvars_2006_, lean_object* v_e_2007_, lean_object* v_a_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v_usedLetOnly_boxed_2015_; uint8_t v_skipConstInApp_boxed_2016_; uint8_t v_skipInstances_boxed_2017_; lean_object* v_res_2018_; 
v_usedLetOnly_boxed_2015_ = lean_unbox(v_usedLetOnly_2003_);
v_skipConstInApp_boxed_2016_ = lean_unbox(v_skipConstInApp_2004_);
v_skipInstances_boxed_2017_ = lean_unbox(v_skipInstances_2005_);
v_res_2018_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_2001_, v_post_2002_, v_usedLetOnly_boxed_2015_, v_skipConstInApp_boxed_2016_, v_skipInstances_boxed_2017_, v_fvars_2006_, v_e_2007_, v_a_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_upperBound_2019_, lean_object* v___x_2020_, lean_object* v_pre_2021_, lean_object* v_post_2022_, lean_object* v_usedLetOnly_2023_, lean_object* v_skipConstInApp_2024_, lean_object* v_skipInstances_2025_, lean_object* v_a_2026_, lean_object* v_b_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_usedLetOnly_boxed_2035_; uint8_t v_skipConstInApp_boxed_2036_; uint8_t v_skipInstances_boxed_2037_; lean_object* v_res_2038_; 
v_usedLetOnly_boxed_2035_ = lean_unbox(v_usedLetOnly_2023_);
v_skipConstInApp_boxed_2036_ = lean_unbox(v_skipConstInApp_2024_);
v_skipInstances_boxed_2037_ = lean_unbox(v_skipInstances_2025_);
v_res_2038_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_upperBound_2019_, v___x_2020_, v_pre_2021_, v_post_2022_, v_usedLetOnly_boxed_2035_, v_skipConstInApp_boxed_2036_, v_skipInstances_boxed_2037_, v_a_2026_, v_b_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec_ref(v___x_2020_);
lean_dec(v_upperBound_2019_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_skipInstances_2039_, lean_object* v_pre_2040_, lean_object* v_post_2041_, lean_object* v_usedLetOnly_2042_, lean_object* v_skipConstInApp_2043_, lean_object* v_x_2044_, lean_object* v_x_2045_, lean_object* v_x_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
uint8_t v_skipInstances_boxed_2054_; uint8_t v_usedLetOnly_boxed_2055_; uint8_t v_skipConstInApp_boxed_2056_; lean_object* v_res_2057_; 
v_skipInstances_boxed_2054_ = lean_unbox(v_skipInstances_2039_);
v_usedLetOnly_boxed_2055_ = lean_unbox(v_usedLetOnly_2042_);
v_skipConstInApp_boxed_2056_ = lean_unbox(v_skipConstInApp_2043_);
v_res_2057_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_skipInstances_boxed_2054_, v_pre_2040_, v_post_2041_, v_usedLetOnly_boxed_2055_, v_skipConstInApp_boxed_2056_, v_x_2044_, v_x_2045_, v_x_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2058_, lean_object* v_x_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_apply_1(v_x_2059_, lean_box(0));
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v___y_2060_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2069_, v_x_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
return v_res_2077_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_unsigned_to_nat(16u);
v___x_2080_ = lean_mk_array(v___x_2079_, v___x_2078_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___x_2081_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2085_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2085_, 0, lean_box(0));
lean_closure_set(v___x_2085_, 1, lean_box(0));
lean_closure_set(v___x_2085_, 2, v___x_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2086_, lean_object* v_pre_2087_, lean_object* v_post_2088_, uint8_t v_usedLetOnly_2089_, uint8_t v_skipConstInApp_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v_a_2099_; lean_object* v_fst_2100_; lean_object* v_snd_2101_; uint8_t v___x_2102_; lean_object* v___x_2103_; 
v___x_2097_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2098_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2097_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref(v___x_2098_);
v_fst_2100_ = lean_ctor_get(v_a_2099_, 0);
lean_inc(v_fst_2100_);
v_snd_2101_ = lean_ctor_get(v_a_2099_, 1);
lean_inc(v_snd_2101_);
lean_dec(v_a_2099_);
v___x_2102_ = 0;
lean_inc(v___y_2095_);
lean_inc_ref(v___y_2094_);
lean_inc(v___y_2093_);
lean_inc_ref(v___y_2092_);
lean_inc(v_fst_2100_);
v___x_2103_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2087_, v_post_2088_, v_usedLetOnly_2089_, v_skipConstInApp_2090_, v___x_2102_, v_input_2086_, v_fst_2100_, v_snd_2101_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v_fst_2105_; lean_object* v_snd_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2125_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2103_);
v_fst_2105_ = lean_ctor_get(v_a_2104_, 0);
lean_inc(v_fst_2105_);
v_snd_2106_ = lean_ctor_get(v_a_2104_, 1);
lean_inc(v_snd_2106_);
lean_dec(v_a_2104_);
v___x_2107_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2107_, 0, lean_box(0));
lean_closure_set(v___x_2107_, 1, lean_box(0));
lean_closure_set(v___x_2107_, 2, v_fst_2100_);
v___x_2108_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2107_, v_snd_2106_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2125_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2125_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_snd_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2123_; 
v_snd_2113_ = lean_ctor_get(v_a_2109_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_a_2109_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; 
v_unused_2124_ = lean_ctor_get(v_a_2109_, 0);
lean_dec(v_unused_2124_);
v___x_2115_ = v_a_2109_;
v_isShared_2116_ = v_isSharedCheck_2123_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_snd_2113_);
lean_dec(v_a_2109_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2123_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v_fst_2105_);
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_fst_2105_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_snd_2113_);
v___x_2118_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2120_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2118_);
v___x_2120_ = v___x_2111_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
else
{
lean_dec(v_fst_2100_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2126_, lean_object* v_pre_2127_, lean_object* v_post_2128_, lean_object* v_usedLetOnly_2129_, lean_object* v_skipConstInApp_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
uint8_t v_usedLetOnly_boxed_2137_; uint8_t v_skipConstInApp_boxed_2138_; lean_object* v_res_2139_; 
v_usedLetOnly_boxed_2137_ = lean_unbox(v_usedLetOnly_2129_);
v_skipConstInApp_boxed_2138_ = lean_unbox(v_skipConstInApp_2130_);
v_res_2139_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2126_, v_pre_2127_, v_post_2128_, v_usedLetOnly_boxed_2137_, v_skipConstInApp_boxed_2138_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
return v_res_2139_;
}
}
static uint64_t _init_l_Lean_Meta_expandCoe___closed__2(void){
_start:
{
uint8_t v___x_2142_; uint64_t v___x_2143_; 
v___x_2142_ = 3;
v___x_2143_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v___x_2150_; uint8_t v_foApprox_2151_; uint8_t v_ctxApprox_2152_; uint8_t v_quasiPatternApprox_2153_; uint8_t v_constApprox_2154_; uint8_t v_isDefEqStuckEx_2155_; uint8_t v_unificationHints_2156_; uint8_t v_proofIrrelevance_2157_; uint8_t v_assignSyntheticOpaque_2158_; uint8_t v_offsetCnstrs_2159_; uint8_t v_etaStruct_2160_; uint8_t v_univApprox_2161_; uint8_t v_iota_2162_; uint8_t v_beta_2163_; uint8_t v_proj_2164_; uint8_t v_zeta_2165_; uint8_t v_zetaDelta_2166_; uint8_t v_zetaUnused_2167_; uint8_t v_zetaHave_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2212_; 
v___x_2150_ = l_Lean_Meta_Context_config(v_a_2145_);
v_foApprox_2151_ = lean_ctor_get_uint8(v___x_2150_, 0);
v_ctxApprox_2152_ = lean_ctor_get_uint8(v___x_2150_, 1);
v_quasiPatternApprox_2153_ = lean_ctor_get_uint8(v___x_2150_, 2);
v_constApprox_2154_ = lean_ctor_get_uint8(v___x_2150_, 3);
v_isDefEqStuckEx_2155_ = lean_ctor_get_uint8(v___x_2150_, 4);
v_unificationHints_2156_ = lean_ctor_get_uint8(v___x_2150_, 5);
v_proofIrrelevance_2157_ = lean_ctor_get_uint8(v___x_2150_, 6);
v_assignSyntheticOpaque_2158_ = lean_ctor_get_uint8(v___x_2150_, 7);
v_offsetCnstrs_2159_ = lean_ctor_get_uint8(v___x_2150_, 8);
v_etaStruct_2160_ = lean_ctor_get_uint8(v___x_2150_, 10);
v_univApprox_2161_ = lean_ctor_get_uint8(v___x_2150_, 11);
v_iota_2162_ = lean_ctor_get_uint8(v___x_2150_, 12);
v_beta_2163_ = lean_ctor_get_uint8(v___x_2150_, 13);
v_proj_2164_ = lean_ctor_get_uint8(v___x_2150_, 14);
v_zeta_2165_ = lean_ctor_get_uint8(v___x_2150_, 15);
v_zetaDelta_2166_ = lean_ctor_get_uint8(v___x_2150_, 16);
v_zetaUnused_2167_ = lean_ctor_get_uint8(v___x_2150_, 17);
v_zetaHave_2168_ = lean_ctor_get_uint8(v___x_2150_, 18);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2170_ = v___x_2150_;
v_isShared_2171_ = v_isSharedCheck_2212_;
goto v_resetjp_2169_;
}
else
{
lean_dec(v___x_2150_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2212_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
uint8_t v_trackZetaDelta_2172_; lean_object* v_zetaDeltaSet_2173_; lean_object* v_lctx_2174_; lean_object* v_localInstances_2175_; lean_object* v_defEqCtx_x3f_2176_; lean_object* v_synthPendingDepth_2177_; lean_object* v_canUnfold_x3f_2178_; uint8_t v_univApprox_2179_; uint8_t v_inTypeClassResolution_2180_; uint8_t v_cacheInferType_2181_; uint8_t v___x_2182_; lean_object* v_config_2184_; 
v_trackZetaDelta_2172_ = lean_ctor_get_uint8(v_a_2145_, sizeof(void*)*7);
v_zetaDeltaSet_2173_ = lean_ctor_get(v_a_2145_, 1);
lean_inc(v_zetaDeltaSet_2173_);
v_lctx_2174_ = lean_ctor_get(v_a_2145_, 2);
lean_inc_ref(v_lctx_2174_);
v_localInstances_2175_ = lean_ctor_get(v_a_2145_, 3);
lean_inc_ref(v_localInstances_2175_);
v_defEqCtx_x3f_2176_ = lean_ctor_get(v_a_2145_, 4);
lean_inc(v_defEqCtx_x3f_2176_);
v_synthPendingDepth_2177_ = lean_ctor_get(v_a_2145_, 5);
lean_inc(v_synthPendingDepth_2177_);
v_canUnfold_x3f_2178_ = lean_ctor_get(v_a_2145_, 6);
lean_inc(v_canUnfold_x3f_2178_);
v_univApprox_2179_ = lean_ctor_get_uint8(v_a_2145_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2180_ = lean_ctor_get_uint8(v_a_2145_, sizeof(void*)*7 + 2);
v_cacheInferType_2181_ = lean_ctor_get_uint8(v_a_2145_, sizeof(void*)*7 + 3);
v___x_2182_ = 3;
if (v_isShared_2171_ == 0)
{
v_config_2184_ = v___x_2170_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 0, v_foApprox_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 1, v_ctxApprox_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 2, v_quasiPatternApprox_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 3, v_constApprox_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 4, v_isDefEqStuckEx_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 5, v_unificationHints_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 6, v_proofIrrelevance_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 7, v_assignSyntheticOpaque_2158_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 8, v_offsetCnstrs_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 10, v_etaStruct_2160_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 11, v_univApprox_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 12, v_iota_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 13, v_beta_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 14, v_proj_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 15, v_zeta_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 16, v_zetaDelta_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 17, v_zetaUnused_2167_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, 18, v_zetaHave_2168_);
v_config_2184_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
uint64_t v___x_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2203_; 
lean_ctor_set_uint8(v_config_2184_, 9, v___x_2182_);
v___x_2185_ = l_Lean_Meta_Context_configKey(v_a_2145_);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_a_2145_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; lean_object* v_unused_2205_; lean_object* v_unused_2206_; lean_object* v_unused_2207_; lean_object* v_unused_2208_; lean_object* v_unused_2209_; lean_object* v_unused_2210_; 
v_unused_2204_ = lean_ctor_get(v_a_2145_, 6);
lean_dec(v_unused_2204_);
v_unused_2205_ = lean_ctor_get(v_a_2145_, 5);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_a_2145_, 4);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_a_2145_, 3);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_a_2145_, 2);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_a_2145_, 1);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_a_2145_, 0);
lean_dec(v_unused_2210_);
v___x_2187_ = v_a_2145_;
v_isShared_2188_ = v_isSharedCheck_2203_;
goto v_resetjp_2186_;
}
else
{
lean_dec(v_a_2145_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2203_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
uint64_t v___x_2189_; uint64_t v___x_2190_; lean_object* v___f_2191_; lean_object* v___f_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; uint64_t v___x_2195_; uint64_t v___x_2196_; uint64_t v_key_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2189_ = 2ULL;
v___x_2190_ = lean_uint64_shift_right(v___x_2185_, v___x_2189_);
v___f_2191_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2192_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2193_ = 0;
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_uint64_shift_left(v___x_2190_, v___x_2189_);
v___x_2196_ = lean_uint64_once(&l_Lean_Meta_expandCoe___closed__2, &l_Lean_Meta_expandCoe___closed__2_once, _init_l_Lean_Meta_expandCoe___closed__2);
v_key_2197_ = lean_uint64_lor(v___x_2195_, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2198_, 0, v_config_2184_);
lean_ctor_set_uint64(v___x_2198_, sizeof(void*)*1, v_key_2197_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2198_);
v___x_2200_ = v___x_2187_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_zetaDeltaSet_2173_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_lctx_2174_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_localInstances_2175_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_defEqCtx_x3f_2176_);
lean_ctor_set(v_reuseFailAlloc_2202_, 5, v_synthPendingDepth_2177_);
lean_ctor_set(v_reuseFailAlloc_2202_, 6, v_canUnfold_x3f_2178_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*7, v_trackZetaDelta_2172_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*7 + 1, v_univApprox_2179_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2180_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*7 + 3, v_cacheInferType_2181_);
v___x_2200_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2144_, v___f_2192_, v___f_2191_, v___x_2193_, v___x_2193_, v___x_2194_, v___x_2200_, v_a_2146_, v_a_2147_, v_a_2148_);
return v___x_2201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_Meta_expandCoe(v_e_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object* v_cls_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg(v_cls_2220_, v___y_2221_, v___y_2224_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2236_, lean_object* v_m_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2237_, v_a_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2240_, lean_object* v_m_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2240_, v_m_2241_, v_a_2242_);
lean_dec(v_a_2242_);
lean_dec_ref(v_m_2241_);
return v_res_2243_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2244_, lean_object* v_x_2245_, lean_object* v_x_2246_){
_start:
{
uint8_t v___x_2247_; 
v___x_2247_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2245_, v_x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_){
_start:
{
uint8_t v_res_2251_; lean_object* v_r_2252_; 
v_res_2251_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2248_, v_x_2249_, v_x_2250_);
lean_dec_ref(v_x_2250_);
v_r_2252_ = lean_box(v_res_2251_);
return v_r_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2253_, lean_object* v_a_2254_, lean_object* v_x_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(v_a_2254_, v_x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2257_, lean_object* v_a_2258_, lean_object* v_x_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6(v_00_u03b2_2257_, v_a_2258_, v_x_2259_);
lean_dec(v_x_2259_);
lean_dec(v_a_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_upperBound_2261_, lean_object* v___x_2262_, lean_object* v_pre_2263_, lean_object* v_post_2264_, uint8_t v_usedLetOnly_2265_, uint8_t v_skipConstInApp_2266_, uint8_t v_skipInstances_2267_, lean_object* v___x_2268_, lean_object* v_inst_2269_, lean_object* v_R_2270_, lean_object* v_a_2271_, lean_object* v_b_2272_, lean_object* v_c_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_upperBound_2261_, v___x_2262_, v_pre_2263_, v_post_2264_, v_usedLetOnly_2265_, v_skipConstInApp_2266_, v_skipInstances_2267_, v_a_2271_, v_b_2272_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object** _args){
lean_object* v_upperBound_2282_ = _args[0];
lean_object* v___x_2283_ = _args[1];
lean_object* v_pre_2284_ = _args[2];
lean_object* v_post_2285_ = _args[3];
lean_object* v_usedLetOnly_2286_ = _args[4];
lean_object* v_skipConstInApp_2287_ = _args[5];
lean_object* v_skipInstances_2288_ = _args[6];
lean_object* v___x_2289_ = _args[7];
lean_object* v_inst_2290_ = _args[8];
lean_object* v_R_2291_ = _args[9];
lean_object* v_a_2292_ = _args[10];
lean_object* v_b_2293_ = _args[11];
lean_object* v_c_2294_ = _args[12];
lean_object* v___y_2295_ = _args[13];
lean_object* v___y_2296_ = _args[14];
lean_object* v___y_2297_ = _args[15];
lean_object* v___y_2298_ = _args[16];
lean_object* v___y_2299_ = _args[17];
lean_object* v___y_2300_ = _args[18];
lean_object* v___y_2301_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2302_; uint8_t v_skipConstInApp_boxed_2303_; uint8_t v_skipInstances_boxed_2304_; lean_object* v_res_2305_; 
v_usedLetOnly_boxed_2302_ = lean_unbox(v_usedLetOnly_2286_);
v_skipConstInApp_boxed_2303_ = lean_unbox(v_skipConstInApp_2287_);
v_skipInstances_boxed_2304_ = lean_unbox(v_skipInstances_2288_);
v_res_2305_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_upperBound_2282_, v___x_2283_, v_pre_2284_, v_post_2285_, v_usedLetOnly_boxed_2302_, v_skipConstInApp_boxed_2303_, v_skipInstances_boxed_2304_, v___x_2289_, v_inst_2290_, v_R_2291_, v_a_2292_, v_b_2293_, v_c_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___x_2289_);
lean_dec_ref(v___x_2283_);
lean_dec(v_upperBound_2282_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_00_u03b2_2306_, lean_object* v_m_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_m_2307_, v_a_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_00_u03b2_2310_, lean_object* v_m_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_00_u03b2_2310_, v_m_2311_, v_a_2312_);
lean_dec_ref(v_a_2312_);
lean_dec_ref(v_m_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17(lean_object* v_00_u03b1_2314_, lean_object* v_name_2315_, uint8_t v_bi_2316_, lean_object* v_type_2317_, lean_object* v_k_2318_, uint8_t v_kind_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg(v_name_2315_, v_bi_2316_, v_type_2317_, v_k_2318_, v_kind_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___boxed(lean_object* v_00_u03b1_2328_, lean_object* v_name_2329_, lean_object* v_bi_2330_, lean_object* v_type_2331_, lean_object* v_k_2332_, lean_object* v_kind_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
uint8_t v_bi_boxed_2341_; uint8_t v_kind_boxed_2342_; lean_object* v_res_2343_; 
v_bi_boxed_2341_ = lean_unbox(v_bi_2330_);
v_kind_boxed_2342_ = lean_unbox(v_kind_2333_);
v_res_2343_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17(v_00_u03b1_2328_, v_name_2329_, v_bi_boxed_2341_, v_type_2331_, v_k_2332_, v_kind_boxed_2342_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20(lean_object* v_00_u03b1_2344_, lean_object* v_name_2345_, lean_object* v_type_2346_, lean_object* v_val_2347_, lean_object* v_k_2348_, uint8_t v_nondep_2349_, uint8_t v_kind_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___redArg(v_name_2345_, v_type_2346_, v_val_2347_, v_k_2348_, v_nondep_2349_, v_kind_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2359_, lean_object* v_name_2360_, lean_object* v_type_2361_, lean_object* v_val_2362_, lean_object* v_k_2363_, lean_object* v_nondep_2364_, lean_object* v_kind_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
uint8_t v_nondep_boxed_2373_; uint8_t v_kind_boxed_2374_; lean_object* v_res_2375_; 
v_nondep_boxed_2373_ = lean_unbox(v_nondep_2364_);
v_kind_boxed_2374_ = lean_unbox(v_kind_2365_);
v_res_2375_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20(v_00_u03b1_2359_, v_name_2360_, v_type_2361_, v_val_2362_, v_k_2363_, v_nondep_boxed_2373_, v_kind_boxed_2374_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23(lean_object* v_00_u03b1_2376_, lean_object* v_ref_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg(v_ref_2377_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2384_, lean_object* v_ref_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23(v_00_u03b1_2384_, v_ref_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b1_2392_, lean_object* v_x_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_x_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___boxed(lean_object* v_00_u03b1_2402_, lean_object* v_x_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(v_00_u03b1_2402_, v_x_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18(lean_object* v_00_u03b2_2412_, lean_object* v_m_2413_, lean_object* v_a_2414_, lean_object* v_b_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v_m_2413_, v_a_2414_, v_b_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2417_, lean_object* v_x_2418_, size_t v_x_2419_, lean_object* v_x_2420_){
_start:
{
uint8_t v___x_2421_; 
v___x_2421_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2418_, v_x_2419_, v_x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2422_, lean_object* v_x_2423_, lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
size_t v_x_39442__boxed_2426_; uint8_t v_res_2427_; lean_object* v_r_2428_; 
v_x_39442__boxed_2426_ = lean_unbox_usize(v_x_2424_);
lean_dec(v_x_2424_);
v_res_2427_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2422_, v_x_2423_, v_x_39442__boxed_2426_, v_x_2425_);
lean_dec_ref(v_x_2425_);
v_r_2428_ = lean_box(v_res_2427_);
return v_r_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15(lean_object* v_00_u03b2_2429_, lean_object* v_a_2430_, lean_object* v_x_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg(v_a_2430_, v_x_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2433_, lean_object* v_a_2434_, lean_object* v_x_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15(v_00_u03b2_2433_, v_a_2434_, v_x_2435_);
lean_dec(v_x_2435_);
lean_dec_ref(v_a_2434_);
return v_res_2436_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25(lean_object* v_00_u03b2_2437_, lean_object* v_a_2438_, lean_object* v_x_2439_){
_start:
{
uint8_t v___x_2440_; 
v___x_2440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___redArg(v_a_2438_, v_x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___boxed(lean_object* v_00_u03b2_2441_, lean_object* v_a_2442_, lean_object* v_x_2443_){
_start:
{
uint8_t v_res_2444_; lean_object* v_r_2445_; 
v_res_2444_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25(v_00_u03b2_2441_, v_a_2442_, v_x_2443_);
lean_dec(v_x_2443_);
lean_dec_ref(v_a_2442_);
v_r_2445_ = lean_box(v_res_2444_);
return v_r_2445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26(lean_object* v_00_u03b2_2446_, lean_object* v_data_2447_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(v_data_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27(lean_object* v_00_u03b2_2449_, lean_object* v_a_2450_, lean_object* v_b_2451_, lean_object* v_x_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_a_2450_, v_b_2451_, v_x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2454_, lean_object* v_keys_2455_, lean_object* v_vals_2456_, lean_object* v_heq_2457_, lean_object* v_i_2458_, lean_object* v_k_2459_){
_start:
{
uint8_t v___x_2460_; 
v___x_2460_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_2455_, v_i_2458_, v_k_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_2461_, lean_object* v_keys_2462_, lean_object* v_vals_2463_, lean_object* v_heq_2464_, lean_object* v_i_2465_, lean_object* v_k_2466_){
_start:
{
uint8_t v_res_2467_; lean_object* v_r_2468_; 
v_res_2467_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_2461_, v_keys_2462_, v_vals_2463_, v_heq_2464_, v_i_2465_, v_k_2466_);
lean_dec_ref(v_k_2466_);
lean_dec_ref(v_vals_2463_);
lean_dec_ref(v_keys_2462_);
v_r_2468_ = lean_box(v_res_2467_);
return v_r_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28(lean_object* v_00_u03b2_2469_, lean_object* v_i_2470_, lean_object* v_source_2471_, lean_object* v_target_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28___redArg(v_i_2470_, v_source_2471_, v_target_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28_spec__29(lean_object* v_00_u03b2_2474_, lean_object* v_x_2475_, lean_object* v_x_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28_spec__29___redArg(v_x_2475_, v_x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2478_, lean_object* v_decl_2479_, lean_object* v_ref_2480_){
_start:
{
lean_object* v_defValue_2482_; lean_object* v_descr_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2510_; 
v_defValue_2482_ = lean_ctor_get(v_decl_2479_, 0);
v_descr_2483_ = lean_ctor_get(v_decl_2479_, 1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_decl_2479_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2485_ = v_decl_2479_;
v_isShared_2486_ = v_isSharedCheck_2510_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_descr_2483_);
lean_inc(v_defValue_2482_);
lean_dec(v_decl_2479_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2510_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; uint8_t v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2487_ = lean_alloc_ctor(1, 0, 1);
v___x_2488_ = lean_unbox(v_defValue_2482_);
lean_ctor_set_uint8(v___x_2487_, 0, v___x_2488_);
lean_inc(v_name_2478_);
v___x_2489_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2489_, 0, v_name_2478_);
lean_ctor_set(v___x_2489_, 1, v_ref_2480_);
lean_ctor_set(v___x_2489_, 2, v___x_2487_);
lean_ctor_set(v___x_2489_, 3, v_descr_2483_);
lean_inc(v_name_2478_);
v___x_2490_ = lean_register_option(v_name_2478_, v___x_2489_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2500_; 
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v___x_2490_, 0);
lean_dec(v_unused_2501_);
v___x_2492_ = v___x_2490_;
v_isShared_2493_ = v_isSharedCheck_2500_;
goto v_resetjp_2491_;
}
else
{
lean_dec(v___x_2490_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2500_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v_defValue_2482_);
lean_ctor_set(v___x_2485_, 0, v_name_2478_);
v___x_2495_ = v___x_2485_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_name_2478_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_defValue_2482_);
v___x_2495_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2497_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2495_);
v___x_2497_ = v___x_2492_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_del_object(v___x_2485_);
lean_dec(v_defValue_2482_);
lean_dec(v_name_2478_);
v_a_2502_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2490_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2490_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2511_, lean_object* v_decl_2512_, lean_object* v_ref_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2511_, v_decl_2512_, v_ref_2513_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2529_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2530_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2531_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2532_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2529_, v___x_2530_, v___x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_ref_2541_; lean_object* v___x_2542_; lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2551_; 
v_ref_2541_ = lean_ctor_get(v___y_2538_, 5);
v___x_2542_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__6(v_msg_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_inc(v_ref_2541_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v_ref_2541_);
lean_ctor_set(v___x_2547_, 1, v_a_2543_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set_tag(v___x_2545_, 1);
lean_ctor_set(v___x_2545_, 0, v___x_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
return v_res_2558_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2567_ = l_Lean_stringToMessageData(v___x_2566_);
return v___x_2567_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2570_ = l_Lean_stringToMessageData(v___x_2569_);
return v___x_2570_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2573_ = l_Lean_stringToMessageData(v___x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2574_, lean_object* v_expectedType_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v___x_2581_; 
lean_inc(v_a_2579_);
lean_inc_ref(v_a_2578_);
lean_inc(v_a_2577_);
lean_inc_ref(v_a_2576_);
lean_inc_ref(v_expr_2574_);
v___x_2581_ = lean_infer_type(v_expr_2574_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2583_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref(v___x_2581_);
lean_inc(v_a_2579_);
lean_inc_ref(v_a_2578_);
lean_inc(v_a_2577_);
lean_inc_ref(v_a_2576_);
lean_inc(v_a_2582_);
v___x_2583_ = l_Lean_Meta_getLevel(v_a_2582_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref(v___x_2583_);
lean_inc(v_a_2579_);
lean_inc_ref(v_a_2578_);
lean_inc(v_a_2577_);
lean_inc_ref(v_a_2576_);
lean_inc_ref(v_expectedType_2575_);
v___x_2585_ = l_Lean_Meta_getLevel(v_expectedType_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref(v___x_2585_);
v___x_2587_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2588_ = lean_box(0);
v___x_2589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2589_, 0, v_a_2586_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2590_, 0, v_a_2584_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
lean_inc_ref(v___x_2590_);
v___x_2591_ = l_Lean_mkConst(v___x_2587_, v___x_2590_);
v___x_2592_ = lean_unsigned_to_nat(3u);
v___x_2593_ = lean_mk_empty_array_with_capacity(v___x_2592_);
lean_inc(v_a_2582_);
v___x_2594_ = lean_array_push(v___x_2593_, v_a_2582_);
lean_inc_ref(v_expr_2574_);
v___x_2595_ = lean_array_push(v___x_2594_, v_expr_2574_);
lean_inc_ref(v_expectedType_2575_);
v___x_2596_ = lean_array_push(v___x_2595_, v_expectedType_2575_);
v___x_2597_ = l_Lean_mkAppN(v___x_2591_, v___x_2596_);
lean_dec_ref(v___x_2596_);
v___x_2598_ = lean_box(0);
lean_inc(v_a_2579_);
lean_inc_ref(v_a_2578_);
lean_inc(v_a_2577_);
lean_inc_ref(v_a_2576_);
v___x_2599_ = l_Lean_Meta_trySynthInstance(v___x_2597_, v___x_2598_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2697_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2697_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2697_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
switch(lean_obj_tag(v_a_2600_))
{
case 0:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
lean_dec_ref(v___x_2590_);
lean_dec(v_a_2582_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_expectedType_2575_);
lean_dec_ref(v_expr_2574_);
v___x_2604_ = lean_box(0);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2604_);
v___x_2606_ = v___x_2602_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
case 1:
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2692_; 
lean_del_object(v___x_2602_);
v_a_2608_ = lean_ctor_get(v_a_2600_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_a_2600_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2610_ = v_a_2600_;
v_isShared_2611_ = v_isSharedCheck_2692_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v_a_2600_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2692_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2612_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2613_ = l_Lean_mkConst(v___x_2612_, v___x_2590_);
v___x_2614_ = lean_unsigned_to_nat(4u);
v___x_2615_ = lean_mk_empty_array_with_capacity(v___x_2614_);
v___x_2616_ = lean_array_push(v___x_2615_, v_a_2582_);
lean_inc_ref(v_expr_2574_);
v___x_2617_ = lean_array_push(v___x_2616_, v_expr_2574_);
lean_inc_ref(v_expectedType_2575_);
v___x_2618_ = lean_array_push(v___x_2617_, v_expectedType_2575_);
v___x_2619_ = lean_array_push(v___x_2618_, v_a_2608_);
v___x_2620_ = l_Lean_mkAppN(v___x_2613_, v___x_2619_);
lean_dec_ref(v___x_2619_);
lean_inc(v_a_2579_);
lean_inc_ref(v_a_2578_);
lean_inc(v_a_2577_);
lean_inc_ref(v_a_2576_);
v___x_2621_ = l_Lean_Meta_expandCoe(v___x_2620_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2683_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2683_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2683_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_fst_2633_; lean_object* v___x_2634_; 
v_fst_2633_ = lean_ctor_get(v_a_2622_, 0);
lean_inc(v_a_2579_);
lean_inc_ref(v_a_2578_);
lean_inc(v_a_2577_);
lean_inc_ref(v_a_2576_);
lean_inc(v_fst_2633_);
v___x_2634_ = lean_infer_type(v_fst_2633_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref(v___x_2634_);
lean_inc(v_a_2579_);
lean_inc_ref(v_a_2578_);
lean_inc(v_a_2577_);
lean_inc_ref(v_a_2576_);
lean_inc_ref(v_expectedType_2575_);
v___x_2636_ = l_Lean_Meta_isExprDefEq(v_a_2635_, v_expectedType_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; uint8_t v___x_2638_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2636_);
v___x_2638_ = lean_unbox(v_a_2637_);
lean_dec(v_a_2637_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2664_; 
lean_inc(v_fst_2633_);
lean_del_object(v___x_2624_);
lean_del_object(v___x_2610_);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_a_2622_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; lean_object* v_unused_2666_; 
v_unused_2665_ = lean_ctor_get(v_a_2622_, 1);
lean_dec(v_unused_2665_);
v_unused_2666_ = lean_ctor_get(v_a_2622_, 0);
lean_dec(v_unused_2666_);
v___x_2640_ = v_a_2622_;
v_isShared_2641_ = v_isSharedCheck_2664_;
goto v_resetjp_2639_;
}
else
{
lean_dec(v_a_2622_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2664_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2642_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2643_ = l_Lean_indentExpr(v_expr_2574_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 7);
lean_ctor_set(v___x_2640_, 1, v___x_2643_);
lean_ctor_set(v___x_2640_, 0, v___x_2642_);
v___x_2645_ = v___x_2640_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
v___x_2646_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = l_Lean_indentExpr(v_expectedType_2575_);
v___x_2649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2647_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
v___x_2650_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2649_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l_Lean_indentExpr(v_fst_2633_);
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2651_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2653_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2654_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2654_);
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
}
else
{
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_expectedType_2575_);
lean_dec_ref(v_expr_2574_);
goto v___jp_2626_;
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_del_object(v___x_2624_);
lean_dec(v_a_2622_);
lean_del_object(v___x_2610_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_expectedType_2575_);
lean_dec_ref(v_expr_2574_);
v_a_2667_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2636_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2636_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_del_object(v___x_2624_);
lean_dec(v_a_2622_);
lean_del_object(v___x_2610_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_expectedType_2575_);
lean_dec_ref(v_expr_2574_);
v_a_2675_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2634_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2634_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
v___jp_2626_:
{
lean_object* v___x_2628_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v_a_2622_);
v___x_2628_ = v___x_2610_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2622_);
v___x_2628_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2630_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2628_);
v___x_2630_ = v___x_2624_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
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
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_del_object(v___x_2610_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_expectedType_2575_);
lean_dec_ref(v_expr_2574_);
v_a_2684_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2621_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2621_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
default: 
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
lean_dec_ref(v___x_2590_);
lean_dec(v_a_2582_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_expectedType_2575_);
lean_dec_ref(v_expr_2574_);
v___x_2693_ = lean_box(2);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2693_);
v___x_2695_ = v___x_2602_;
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
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec_ref(v___x_2590_);
lean_dec(v_a_2582_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_expectedType_2575_);
lean_dec_ref(v_expr_2574_);
v_a_2698_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2599_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2599_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
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
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v_a_2584_);
lean_dec(v_a_2582_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_expectedType_2575_);
lean_dec_ref(v_expr_2574_);
v_a_2706_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2585_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2585_);
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
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_a_2582_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_expectedType_2575_);
lean_dec_ref(v_expr_2574_);
v_a_2714_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2583_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2583_);
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
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_expectedType_2575_);
lean_dec_ref(v_expr_2574_);
v_a_2722_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2581_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2581_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2730_, lean_object* v_expectedType_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2730_, v_expectedType_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2738_, lean_object* v_msg_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2746_, lean_object* v_msg_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2746_, v_msg_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2754_, lean_object* v_expectedType_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2754_, v_expectedType_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2786_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2786_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2786_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
switch(lean_obj_tag(v_a_2762_))
{
case 0:
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2766_ = lean_box(0);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2766_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
case 1:
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2781_; 
v_a_2770_ = lean_ctor_get(v_a_2762_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_a_2762_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2772_ = v_a_2762_;
v_isShared_2773_ = v_isSharedCheck_2781_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v_a_2762_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2781_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v_fst_2774_; lean_object* v___x_2776_; 
v_fst_2774_ = lean_ctor_get(v_a_2770_, 0);
lean_inc(v_fst_2774_);
lean_dec(v_a_2770_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v_fst_2774_);
v___x_2776_ = v___x_2772_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_fst_2774_);
v___x_2776_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2776_);
v___x_2778_ = v___x_2764_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
default: 
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2782_ = lean_box(2);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2782_);
v___x_2784_ = v___x_2764_;
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
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v_a_2787_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2761_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2761_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2795_, lean_object* v_expectedType_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2795_, v_expectedType_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
return v_res_2802_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2811_ = l_Lean_stringToMessageData(v___x_2810_);
return v___x_2811_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2814_ = l_Lean_stringToMessageData(v___x_2813_);
return v___x_2814_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2817_ = l_Lean_stringToMessageData(v___x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___x_2824_; 
lean_inc(v_a_2822_);
lean_inc_ref(v_a_2821_);
lean_inc(v_a_2820_);
lean_inc_ref(v_a_2819_);
lean_inc_ref(v_expr_2818_);
v___x_2824_ = lean_infer_type(v_expr_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2826_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref(v___x_2824_);
lean_inc(v_a_2822_);
lean_inc_ref(v_a_2821_);
lean_inc(v_a_2820_);
lean_inc_ref(v_a_2819_);
lean_inc(v_a_2825_);
v___x_2826_ = l_Lean_Meta_getLevel(v_a_2825_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___x_2826_);
v___x_2828_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref(v___x_2828_);
lean_inc(v_a_2829_);
v___x_2830_ = l_Lean_mkSort(v_a_2829_);
lean_inc(v_a_2822_);
lean_inc_ref(v_a_2821_);
lean_inc(v_a_2825_);
v___x_2831_ = l_Lean_mkArrow(v_a_2825_, v___x_2830_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref(v___x_2831_);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2832_);
v___x_2834_ = 0;
v___x_2835_ = lean_box(0);
lean_inc_ref(v_a_2819_);
v___x_2836_ = l_Lean_Meta_mkFreshExprMVar(v___x_2833_, v___x_2834_, v___x_2835_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref(v___x_2836_);
v___x_2838_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2839_ = lean_box(0);
v___x_2840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2840_, 0, v_a_2829_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2841_, 0, v_a_2827_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
lean_inc_ref(v___x_2841_);
v___x_2842_ = l_Lean_Expr_const___override(v___x_2838_, v___x_2841_);
lean_inc(v_a_2837_);
lean_inc(v_a_2825_);
v___x_2843_ = l_Lean_mkAppB(v___x_2842_, v_a_2825_, v_a_2837_);
v___x_2844_ = lean_box(0);
lean_inc(v_a_2822_);
lean_inc_ref(v_a_2821_);
lean_inc(v_a_2820_);
lean_inc_ref(v_a_2819_);
v___x_2845_ = l_Lean_Meta_trySynthInstance(v___x_2843_, v___x_2844_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2932_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2932_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2932_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
if (lean_obj_tag(v_a_2846_) == 1)
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2928_; 
lean_del_object(v___x_2848_);
v_a_2850_ = lean_ctor_get(v_a_2846_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_a_2846_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2852_ = v_a_2846_;
v_isShared_2853_ = v_isSharedCheck_2928_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v_a_2846_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2928_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2854_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2855_ = l_Lean_Expr_const___override(v___x_2854_, v___x_2841_);
lean_inc_ref(v_expr_2818_);
lean_inc(v_a_2850_);
v___x_2856_ = l_Lean_mkApp4(v___x_2855_, v_a_2825_, v_a_2837_, v_a_2850_, v_expr_2818_);
lean_inc(v_a_2822_);
lean_inc_ref(v_a_2821_);
lean_inc(v_a_2820_);
lean_inc_ref(v_a_2819_);
v___x_2857_ = l_Lean_Meta_expandCoe(v___x_2856_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2919_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2919_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2919_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v_fst_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2917_; 
v_fst_2862_ = lean_ctor_get(v_a_2858_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_a_2858_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; 
v_unused_2918_ = lean_ctor_get(v_a_2858_, 1);
lean_dec(v_unused_2918_);
v___x_2864_ = v_a_2858_;
v_isShared_2865_ = v_isSharedCheck_2917_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_fst_2862_);
lean_dec(v_a_2858_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2917_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2873_; 
lean_inc(v_a_2822_);
lean_inc_ref(v_a_2821_);
lean_inc(v_a_2820_);
lean_inc_ref(v_a_2819_);
lean_inc(v_fst_2862_);
v___x_2873_ = lean_infer_type(v_fst_2862_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref(v___x_2873_);
lean_inc(v_a_2822_);
lean_inc_ref(v_a_2821_);
lean_inc(v_a_2820_);
lean_inc_ref(v_a_2819_);
v___x_2875_ = lean_whnf(v_a_2874_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; uint8_t v___x_2877_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = l_Lean_Expr_isForall(v_a_2876_);
lean_dec(v_a_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
lean_del_object(v___x_2860_);
lean_del_object(v___x_2852_);
v___x_2878_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2879_ = l_Lean_indentExpr(v_expr_2818_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set_tag(v___x_2864_, 7);
lean_ctor_set(v___x_2864_, 1, v___x_2879_);
lean_ctor_set(v___x_2864_, 0, v___x_2878_);
v___x_2881_ = v___x_2864_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
v___x_2882_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = l_Lean_indentExpr(v_fst_2862_);
v___x_2885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2887_ = l_Lean_indentExpr(v_a_2850_);
v___x_2888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = l_Lean_MessageData_hint_x27(v___x_2888_);
v___x_2890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2885_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2890_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
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
lean_del_object(v___x_2864_);
lean_dec(v_a_2850_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
goto v___jp_2866_;
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_del_object(v___x_2864_);
lean_dec(v_fst_2862_);
lean_del_object(v___x_2860_);
lean_del_object(v___x_2852_);
lean_dec(v_a_2850_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
v_a_2901_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2875_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2875_);
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
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_del_object(v___x_2864_);
lean_dec(v_fst_2862_);
lean_del_object(v___x_2860_);
lean_del_object(v___x_2852_);
lean_dec(v_a_2850_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
v_a_2909_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2873_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2873_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
v___jp_2866_:
{
lean_object* v___x_2868_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v_fst_2862_);
v___x_2868_ = v___x_2852_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_fst_2862_);
v___x_2868_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2868_);
v___x_2870_ = v___x_2860_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_del_object(v___x_2852_);
lean_dec(v_a_2850_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
v_a_2920_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2857_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2857_);
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
}
else
{
lean_object* v___x_2930_; 
lean_dec(v_a_2846_);
lean_dec_ref(v___x_2841_);
lean_dec(v_a_2837_);
lean_dec(v_a_2825_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2844_);
v___x_2930_ = v___x_2848_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2844_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec_ref(v___x_2841_);
lean_dec(v_a_2837_);
lean_dec(v_a_2825_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
v_a_2933_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2845_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2845_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_a_2829_);
lean_dec(v_a_2827_);
lean_dec(v_a_2825_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
v_a_2941_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2836_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2836_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec(v_a_2829_);
lean_dec(v_a_2827_);
lean_dec(v_a_2825_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
v_a_2949_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2831_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2831_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec(v_a_2827_);
lean_dec(v_a_2825_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
v_a_2957_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2828_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2828_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v_a_2825_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
v_a_2965_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2826_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2826_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_expr_2818_);
v_a_2973_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2824_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2824_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
return v_res_2987_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2996_ = l_Lean_stringToMessageData(v___x_2995_);
return v___x_2996_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2999_ = l_Lean_stringToMessageData(v___x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v___x_3006_; 
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
lean_inc_ref(v_expr_3000_);
v___x_3006_ = lean_infer_type(v_expr_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_3006_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
lean_inc(v_a_3007_);
v___x_3008_ = l_Lean_Meta_getLevel(v_a_3007_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref(v___x_3008_);
v___x_3010_ = l_Lean_Meta_mkFreshLevelMVar(v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
lean_inc(v_a_3011_);
v___x_3012_ = l_Lean_mkSort(v_a_3011_);
v___x_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
v___x_3014_ = 0;
v___x_3015_ = lean_box(0);
lean_inc_ref(v_a_3001_);
v___x_3016_ = l_Lean_Meta_mkFreshExprMVar(v___x_3013_, v___x_3014_, v___x_3015_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref(v___x_3016_);
v___x_3018_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_3019_ = lean_box(0);
v___x_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3020_, 0, v_a_3011_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3021_, 0, v_a_3009_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
lean_inc_ref(v___x_3021_);
v___x_3022_ = l_Lean_Expr_const___override(v___x_3018_, v___x_3021_);
lean_inc(v_a_3017_);
lean_inc(v_a_3007_);
v___x_3023_ = l_Lean_mkAppB(v___x_3022_, v_a_3007_, v_a_3017_);
v___x_3024_ = lean_box(0);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
v___x_3025_ = l_Lean_Meta_trySynthInstance(v___x_3023_, v___x_3024_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3112_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3028_ = v___x_3025_;
v_isShared_3029_ = v_isSharedCheck_3112_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3025_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3112_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
if (lean_obj_tag(v_a_3026_) == 1)
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3108_; 
lean_del_object(v___x_3028_);
v_a_3030_ = lean_ctor_get(v_a_3026_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_a_3026_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3032_ = v_a_3026_;
v_isShared_3033_ = v_isSharedCheck_3108_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v_a_3026_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3108_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3034_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_3035_ = l_Lean_Expr_const___override(v___x_3034_, v___x_3021_);
lean_inc_ref(v_expr_3000_);
lean_inc(v_a_3030_);
v___x_3036_ = l_Lean_mkApp4(v___x_3035_, v_a_3007_, v_a_3017_, v_a_3030_, v_expr_3000_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
v___x_3037_ = l_Lean_Meta_expandCoe(v___x_3036_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3099_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3099_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3099_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_fst_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3097_; 
v_fst_3042_ = lean_ctor_get(v_a_3038_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v_a_3038_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; 
v_unused_3098_ = lean_ctor_get(v_a_3038_, 1);
lean_dec(v_unused_3098_);
v___x_3044_ = v_a_3038_;
v_isShared_3045_ = v_isSharedCheck_3097_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_fst_3042_);
lean_dec(v_a_3038_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3097_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3053_; 
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
lean_inc(v_fst_3042_);
v___x_3053_ = lean_infer_type(v_fst_3042_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref(v___x_3053_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
v___x_3055_ = lean_whnf(v_a_3054_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; uint8_t v___x_3057_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref(v___x_3055_);
v___x_3057_ = l_Lean_Expr_isSort(v_a_3056_);
lean_dec(v_a_3056_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
lean_del_object(v___x_3040_);
lean_del_object(v___x_3032_);
v___x_3058_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3059_ = l_Lean_indentExpr(v_expr_3000_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set_tag(v___x_3044_, 7);
lean_ctor_set(v___x_3044_, 1, v___x_3059_);
lean_ctor_set(v___x_3044_, 0, v___x_3058_);
v___x_3061_ = v___x_3044_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
v___x_3062_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3061_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = l_Lean_indentExpr(v_fst_3042_);
v___x_3065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3067_ = l_Lean_indentExpr(v_a_3030_);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = l_Lean_MessageData_hint_x27(v___x_3068_);
v___x_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3065_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3070_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3071_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3071_);
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
else
{
lean_del_object(v___x_3044_);
lean_dec(v_a_3030_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_expr_3000_);
goto v___jp_3046_;
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_del_object(v___x_3044_);
lean_dec(v_fst_3042_);
lean_del_object(v___x_3040_);
lean_del_object(v___x_3032_);
lean_dec(v_a_3030_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_expr_3000_);
v_a_3081_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3055_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3055_);
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
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_del_object(v___x_3044_);
lean_dec(v_fst_3042_);
lean_del_object(v___x_3040_);
lean_del_object(v___x_3032_);
lean_dec(v_a_3030_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_expr_3000_);
v_a_3089_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3053_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3053_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
v___jp_3046_:
{
lean_object* v___x_3048_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v_fst_3042_);
v___x_3048_ = v___x_3032_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_fst_3042_);
v___x_3048_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3050_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3048_);
v___x_3050_ = v___x_3040_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_del_object(v___x_3032_);
lean_dec(v_a_3030_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_expr_3000_);
v_a_3100_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3037_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3037_);
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
else
{
lean_object* v___x_3110_; 
lean_dec(v_a_3026_);
lean_dec_ref(v___x_3021_);
lean_dec(v_a_3017_);
lean_dec(v_a_3007_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_expr_3000_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3024_);
v___x_3110_ = v___x_3028_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3024_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v___x_3021_);
lean_dec(v_a_3017_);
lean_dec(v_a_3007_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_expr_3000_);
v_a_3113_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3025_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3025_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_a_3011_);
lean_dec(v_a_3009_);
lean_dec(v_a_3007_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_expr_3000_);
v_a_3121_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3016_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3016_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_a_3009_);
lean_dec(v_a_3007_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_expr_3000_);
v_a_3129_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3010_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3010_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_a_3007_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_expr_3000_);
v_a_3137_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3008_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3008_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_expr_3000_);
v_a_3145_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3006_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3006_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v___x_3163_; 
v___x_3163_ = l_Lean_Expr_hasMVar(v_e_3160_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; 
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v_e_3160_);
return v___x_3164_;
}
else
{
lean_object* v___x_3165_; lean_object* v_mctx_3166_; lean_object* v___x_3167_; lean_object* v_fst_3168_; lean_object* v_snd_3169_; lean_object* v___x_3170_; lean_object* v_cache_3171_; lean_object* v_zetaDeltaFVarIds_3172_; lean_object* v_postponed_3173_; lean_object* v_diag_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3183_; 
v___x_3165_ = lean_st_ref_get(v___y_3161_);
v_mctx_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc_ref(v_mctx_3166_);
lean_dec(v___x_3165_);
v___x_3167_ = l_Lean_instantiateMVarsCore(v_mctx_3166_, v_e_3160_);
v_fst_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_fst_3168_);
v_snd_3169_ = lean_ctor_get(v___x_3167_, 1);
lean_inc(v_snd_3169_);
lean_dec_ref(v___x_3167_);
v___x_3170_ = lean_st_ref_take(v___y_3161_);
v_cache_3171_ = lean_ctor_get(v___x_3170_, 1);
v_zetaDeltaFVarIds_3172_ = lean_ctor_get(v___x_3170_, 2);
v_postponed_3173_ = lean_ctor_get(v___x_3170_, 3);
v_diag_3174_ = lean_ctor_get(v___x_3170_, 4);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3183_ == 0)
{
lean_object* v_unused_3184_; 
v_unused_3184_ = lean_ctor_get(v___x_3170_, 0);
lean_dec(v_unused_3184_);
v___x_3176_ = v___x_3170_;
v_isShared_3177_ = v_isSharedCheck_3183_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_diag_3174_);
lean_inc(v_postponed_3173_);
lean_inc(v_zetaDeltaFVarIds_3172_);
lean_inc(v_cache_3171_);
lean_dec(v___x_3170_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3183_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 0, v_snd_3169_);
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_snd_3169_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_cache_3171_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_zetaDeltaFVarIds_3172_);
lean_ctor_set(v_reuseFailAlloc_3182_, 3, v_postponed_3173_);
lean_ctor_set(v_reuseFailAlloc_3182_, 4, v_diag_3174_);
v___x_3179_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = lean_st_ref_set(v___y_3161_, v___x_3179_);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_fst_3168_);
return v___x_3181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3185_, v___y_3186_);
lean_dec(v___y_3186_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3189_, v___y_3191_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
return v_res_3202_;
}
}
static uint64_t _init_l_Lean_Meta_isTypeApp_x3f___closed__0(void){
_start:
{
uint8_t v___x_3203_; uint64_t v___x_3204_; 
v___x_3203_ = 2;
v___x_3204_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v___x_3211_; uint8_t v_foApprox_3212_; uint8_t v_ctxApprox_3213_; uint8_t v_quasiPatternApprox_3214_; uint8_t v_constApprox_3215_; uint8_t v_isDefEqStuckEx_3216_; uint8_t v_unificationHints_3217_; uint8_t v_proofIrrelevance_3218_; uint8_t v_assignSyntheticOpaque_3219_; uint8_t v_offsetCnstrs_3220_; uint8_t v_etaStruct_3221_; uint8_t v_univApprox_3222_; uint8_t v_iota_3223_; uint8_t v_beta_3224_; uint8_t v_proj_3225_; uint8_t v_zeta_3226_; uint8_t v_zetaDelta_3227_; uint8_t v_zetaUnused_3228_; uint8_t v_zetaHave_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3307_; 
v___x_3211_ = l_Lean_Meta_Context_config(v_a_3206_);
v_foApprox_3212_ = lean_ctor_get_uint8(v___x_3211_, 0);
v_ctxApprox_3213_ = lean_ctor_get_uint8(v___x_3211_, 1);
v_quasiPatternApprox_3214_ = lean_ctor_get_uint8(v___x_3211_, 2);
v_constApprox_3215_ = lean_ctor_get_uint8(v___x_3211_, 3);
v_isDefEqStuckEx_3216_ = lean_ctor_get_uint8(v___x_3211_, 4);
v_unificationHints_3217_ = lean_ctor_get_uint8(v___x_3211_, 5);
v_proofIrrelevance_3218_ = lean_ctor_get_uint8(v___x_3211_, 6);
v_assignSyntheticOpaque_3219_ = lean_ctor_get_uint8(v___x_3211_, 7);
v_offsetCnstrs_3220_ = lean_ctor_get_uint8(v___x_3211_, 8);
v_etaStruct_3221_ = lean_ctor_get_uint8(v___x_3211_, 10);
v_univApprox_3222_ = lean_ctor_get_uint8(v___x_3211_, 11);
v_iota_3223_ = lean_ctor_get_uint8(v___x_3211_, 12);
v_beta_3224_ = lean_ctor_get_uint8(v___x_3211_, 13);
v_proj_3225_ = lean_ctor_get_uint8(v___x_3211_, 14);
v_zeta_3226_ = lean_ctor_get_uint8(v___x_3211_, 15);
v_zetaDelta_3227_ = lean_ctor_get_uint8(v___x_3211_, 16);
v_zetaUnused_3228_ = lean_ctor_get_uint8(v___x_3211_, 17);
v_zetaHave_3229_ = lean_ctor_get_uint8(v___x_3211_, 18);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3231_ = v___x_3211_;
v_isShared_3232_ = v_isSharedCheck_3307_;
goto v_resetjp_3230_;
}
else
{
lean_dec(v___x_3211_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3307_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
uint8_t v_trackZetaDelta_3233_; lean_object* v_zetaDeltaSet_3234_; lean_object* v_lctx_3235_; lean_object* v_localInstances_3236_; lean_object* v_defEqCtx_x3f_3237_; lean_object* v_synthPendingDepth_3238_; lean_object* v_canUnfold_x3f_3239_; uint8_t v_univApprox_3240_; uint8_t v_inTypeClassResolution_3241_; uint8_t v_cacheInferType_3242_; uint8_t v___x_3243_; lean_object* v_config_3245_; 
v_trackZetaDelta_3233_ = lean_ctor_get_uint8(v_a_3206_, sizeof(void*)*7);
v_zetaDeltaSet_3234_ = lean_ctor_get(v_a_3206_, 1);
lean_inc(v_zetaDeltaSet_3234_);
v_lctx_3235_ = lean_ctor_get(v_a_3206_, 2);
lean_inc_ref(v_lctx_3235_);
v_localInstances_3236_ = lean_ctor_get(v_a_3206_, 3);
lean_inc_ref(v_localInstances_3236_);
v_defEqCtx_x3f_3237_ = lean_ctor_get(v_a_3206_, 4);
lean_inc(v_defEqCtx_x3f_3237_);
v_synthPendingDepth_3238_ = lean_ctor_get(v_a_3206_, 5);
lean_inc(v_synthPendingDepth_3238_);
v_canUnfold_x3f_3239_ = lean_ctor_get(v_a_3206_, 6);
lean_inc(v_canUnfold_x3f_3239_);
v_univApprox_3240_ = lean_ctor_get_uint8(v_a_3206_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3241_ = lean_ctor_get_uint8(v_a_3206_, sizeof(void*)*7 + 2);
v_cacheInferType_3242_ = lean_ctor_get_uint8(v_a_3206_, sizeof(void*)*7 + 3);
v___x_3243_ = 2;
if (v_isShared_3232_ == 0)
{
v_config_3245_ = v___x_3231_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 0, v_foApprox_3212_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 1, v_ctxApprox_3213_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 2, v_quasiPatternApprox_3214_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 3, v_constApprox_3215_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 4, v_isDefEqStuckEx_3216_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 5, v_unificationHints_3217_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 6, v_proofIrrelevance_3218_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 7, v_assignSyntheticOpaque_3219_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 8, v_offsetCnstrs_3220_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 10, v_etaStruct_3221_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 11, v_univApprox_3222_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 12, v_iota_3223_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 13, v_beta_3224_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 14, v_proj_3225_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 15, v_zeta_3226_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 16, v_zetaDelta_3227_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 17, v_zetaUnused_3228_);
lean_ctor_set_uint8(v_reuseFailAlloc_3306_, 18, v_zetaHave_3229_);
v_config_3245_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
uint64_t v___x_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3298_; 
lean_ctor_set_uint8(v_config_3245_, 9, v___x_3243_);
v___x_3246_ = l_Lean_Meta_Context_configKey(v_a_3206_);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_a_3206_);
if (v_isSharedCheck_3298_ == 0)
{
lean_object* v_unused_3299_; lean_object* v_unused_3300_; lean_object* v_unused_3301_; lean_object* v_unused_3302_; lean_object* v_unused_3303_; lean_object* v_unused_3304_; lean_object* v_unused_3305_; 
v_unused_3299_ = lean_ctor_get(v_a_3206_, 6);
lean_dec(v_unused_3299_);
v_unused_3300_ = lean_ctor_get(v_a_3206_, 5);
lean_dec(v_unused_3300_);
v_unused_3301_ = lean_ctor_get(v_a_3206_, 4);
lean_dec(v_unused_3301_);
v_unused_3302_ = lean_ctor_get(v_a_3206_, 3);
lean_dec(v_unused_3302_);
v_unused_3303_ = lean_ctor_get(v_a_3206_, 2);
lean_dec(v_unused_3303_);
v_unused_3304_ = lean_ctor_get(v_a_3206_, 1);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_a_3206_, 0);
lean_dec(v_unused_3305_);
v___x_3248_ = v_a_3206_;
v_isShared_3249_ = v_isSharedCheck_3298_;
goto v_resetjp_3247_;
}
else
{
lean_dec(v_a_3206_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3298_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
uint64_t v___x_3250_; uint64_t v___x_3251_; uint64_t v___x_3252_; uint64_t v___x_3253_; uint64_t v_key_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3250_ = 2ULL;
v___x_3251_ = lean_uint64_shift_right(v___x_3246_, v___x_3250_);
v___x_3252_ = lean_uint64_shift_left(v___x_3251_, v___x_3250_);
v___x_3253_ = lean_uint64_once(&l_Lean_Meta_isTypeApp_x3f___closed__0, &l_Lean_Meta_isTypeApp_x3f___closed__0_once, _init_l_Lean_Meta_isTypeApp_x3f___closed__0);
v_key_3254_ = lean_uint64_lor(v___x_3252_, v___x_3253_);
v___x_3255_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3255_, 0, v_config_3245_);
lean_ctor_set_uint64(v___x_3255_, sizeof(void*)*1, v_key_3254_);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v___x_3255_);
v___x_3257_ = v___x_3248_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_zetaDeltaSet_3234_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_lctx_3235_);
lean_ctor_set(v_reuseFailAlloc_3297_, 3, v_localInstances_3236_);
lean_ctor_set(v_reuseFailAlloc_3297_, 4, v_defEqCtx_x3f_3237_);
lean_ctor_set(v_reuseFailAlloc_3297_, 5, v_synthPendingDepth_3238_);
lean_ctor_set(v_reuseFailAlloc_3297_, 6, v_canUnfold_x3f_3239_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*7, v_trackZetaDelta_3233_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*7 + 1, v_univApprox_3240_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3241_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*7 + 3, v_cacheInferType_3242_);
v___x_3257_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; 
lean_inc(v_a_3207_);
v___x_3258_ = lean_whnf(v_type_3205_, v___x_3257_, v_a_3207_, v_a_3208_, v_a_3209_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3288_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3288_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3288_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
if (lean_obj_tag(v_a_3259_) == 5)
{
lean_object* v_fn_3263_; lean_object* v_arg_3264_; lean_object* v___x_3265_; lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3283_; 
lean_del_object(v___x_3261_);
v_fn_3263_ = lean_ctor_get(v_a_3259_, 0);
lean_inc_ref(v_fn_3263_);
v_arg_3264_ = lean_ctor_get(v_a_3259_, 1);
lean_inc_ref(v_arg_3264_);
lean_dec_ref(v_a_3259_);
v___x_3265_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3263_, v_a_3207_);
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3283_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3283_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3282_; 
v___x_3270_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3264_, v_a_3207_);
lean_dec(v_a_3207_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3282_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3282_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3277_; 
v___x_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3275_, 0, v_a_3266_);
lean_ctor_set(v___x_3275_, 1, v_a_3271_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set_tag(v___x_3268_, 1);
lean_ctor_set(v___x_3268_, 0, v___x_3275_);
v___x_3277_ = v___x_3268_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3275_);
v___x_3277_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
lean_object* v___x_3279_; 
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3277_);
v___x_3279_ = v___x_3273_;
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
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3286_; 
lean_dec(v_a_3259_);
lean_dec(v_a_3207_);
v___x_3284_ = lean_box(0);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3284_);
v___x_3286_ = v___x_3261_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec(v_a_3207_);
v_a_3289_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3258_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3258_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_Meta_isTypeApp_x3f(v_type_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v___x_3321_; 
lean_inc(v_a_3319_);
lean_inc_ref(v_a_3318_);
lean_inc(v_a_3317_);
lean_inc_ref(v_a_3316_);
v___x_3321_ = l_Lean_Meta_isTypeApp_x3f(v_type_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3357_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3357_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3357_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
if (lean_obj_tag(v_a_3322_) == 1)
{
lean_object* v_val_3326_; lean_object* v_fst_3327_; lean_object* v___x_3328_; 
lean_del_object(v___x_3324_);
v_val_3326_ = lean_ctor_get(v_a_3322_, 0);
lean_inc(v_val_3326_);
lean_dec_ref(v_a_3322_);
v_fst_3327_ = lean_ctor_get(v_val_3326_, 0);
lean_inc(v_fst_3327_);
lean_dec(v_val_3326_);
v___x_3328_ = l_Lean_Meta_isMonad_x3f(v_fst_3327_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3343_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3343_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3343_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
if (lean_obj_tag(v_a_3329_) == 0)
{
uint8_t v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3333_ = 0;
v___x_3334_ = lean_box(v___x_3333_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3334_);
v___x_3336_ = v___x_3331_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
else
{
uint8_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3341_; 
lean_dec_ref(v_a_3329_);
v___x_3338_ = 1;
v___x_3339_ = lean_box(v___x_3338_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3339_);
v___x_3341_ = v___x_3331_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
v_a_3344_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3328_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3328_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
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
uint8_t v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
lean_dec(v_a_3322_);
lean_dec(v_a_3319_);
lean_dec_ref(v_a_3318_);
lean_dec(v_a_3317_);
lean_dec_ref(v_a_3316_);
v___x_3352_ = 0;
v___x_3353_ = lean_box(v___x_3352_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3353_);
v___x_3355_ = v___x_3324_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec(v_a_3319_);
lean_dec_ref(v_a_3318_);
lean_dec(v_a_3317_);
lean_dec_ref(v_a_3316_);
v_a_3358_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3321_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3321_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Meta_isMonadApp(v_type_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3373_, lean_object* v_opt_3374_){
_start:
{
lean_object* v_name_3375_; lean_object* v_defValue_3376_; lean_object* v_map_3377_; lean_object* v___x_3378_; 
v_name_3375_ = lean_ctor_get(v_opt_3374_, 0);
v_defValue_3376_ = lean_ctor_get(v_opt_3374_, 1);
v_map_3377_ = lean_ctor_get(v_opts_3373_, 0);
v___x_3378_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3377_, v_name_3375_);
if (lean_obj_tag(v___x_3378_) == 0)
{
uint8_t v___x_3379_; 
v___x_3379_ = lean_unbox(v_defValue_3376_);
return v___x_3379_;
}
else
{
lean_object* v_val_3380_; 
v_val_3380_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_val_3380_);
lean_dec_ref(v___x_3378_);
if (lean_obj_tag(v_val_3380_) == 1)
{
uint8_t v_v_3381_; 
v_v_3381_ = lean_ctor_get_uint8(v_val_3380_, 0);
lean_dec_ref(v_val_3380_);
return v_v_3381_;
}
else
{
uint8_t v___x_3382_; 
lean_dec(v_val_3380_);
v___x_3382_ = lean_unbox(v_defValue_3376_);
return v___x_3382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3383_, lean_object* v_opt_3384_){
_start:
{
uint8_t v_res_3385_; lean_object* v_r_3386_; 
v_res_3385_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3383_, v_opt_3384_);
lean_dec_ref(v_opt_3384_);
lean_dec_ref(v_opts_3383_);
v_r_3386_ = lean_box(v_res_3385_);
return v_r_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_x_3397_);
return v_res_3403_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = l_Lean_mkBVar(v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3426_, lean_object* v_expectedType_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v___y_3434_; uint8_t v___y_3435_; lean_object* v_a_3440_; lean_object* v___y_3444_; lean_object* v___x_3454_; lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3858_; 
v___x_3454_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3427_, v_a_3429_);
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3858_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3858_;
goto v_resetjp_3456_;
}
v___jp_3433_:
{
if (v___y_3435_ == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
lean_dec_ref(v___y_3434_);
v___x_3436_ = lean_box(0);
v___x_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
return v___x_3437_;
}
else
{
lean_object* v___x_3438_; 
v___x_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___y_3434_);
return v___x_3438_;
}
}
v___jp_3439_:
{
uint8_t v___x_3441_; 
v___x_3441_ = l_Lean_Exception_isInterrupt(v_a_3440_);
if (v___x_3441_ == 0)
{
uint8_t v___x_3442_; 
lean_inc_ref(v_a_3440_);
v___x_3442_ = l_Lean_Exception_isRuntime(v_a_3440_);
v___y_3434_ = v_a_3440_;
v___y_3435_ = v___x_3442_;
goto v___jp_3433_;
}
else
{
v___y_3434_ = v_a_3440_;
v___y_3435_ = v___x_3441_;
goto v___jp_3433_;
}
}
v___jp_3443_:
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3453_; 
v_a_3445_ = lean_ctor_get(v___y_3444_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___y_3444_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3447_ = v___y_3444_;
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___y_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v_a_3449_; lean_object* v___x_3451_; 
v_a_3449_ = lean_ctor_get(v_a_3445_, 0);
lean_inc(v_a_3449_);
lean_dec(v_a_3445_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v_a_3449_);
v___x_3451_ = v___x_3447_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; 
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc_ref(v_e_3426_);
v___x_3459_ = lean_infer_type(v_e_3426_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3849_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref(v___x_3459_);
v___x_3461_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3460_, v_a_3429_);
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3849_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3849_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; 
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_a_3455_);
v___x_3466_ = l_Lean_Meta_isTypeApp_x3f(v_a_3455_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3840_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3840_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3840_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
if (lean_obj_tag(v_a_3467_) == 1)
{
lean_object* v_val_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3835_; 
lean_del_object(v___x_3469_);
v_val_3471_ = lean_ctor_get(v_a_3467_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_a_3467_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3473_ = v_a_3467_;
v_isShared_3474_ = v_isSharedCheck_3835_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_val_3471_);
lean_dec(v_a_3467_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3835_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v_fst_3475_; lean_object* v_snd_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3834_; 
v_fst_3475_ = lean_ctor_get(v_val_3471_, 0);
v_snd_3476_ = lean_ctor_get(v_val_3471_, 1);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_val_3471_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3478_ = v_val_3471_;
v_isShared_3479_ = v_isSharedCheck_3834_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_snd_3476_);
lean_inc(v_fst_3475_);
lean_dec(v_val_3471_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3834_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; 
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_a_3462_);
v___x_3480_ = l_Lean_Meta_isTypeApp_x3f(v_a_3462_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3825_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3825_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3825_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
if (lean_obj_tag(v_a_3481_) == 1)
{
lean_object* v_val_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3820_; 
lean_del_object(v___x_3483_);
v_val_3485_ = lean_ctor_get(v_a_3481_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_a_3481_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3487_ = v_a_3481_;
v_isShared_3488_ = v_isSharedCheck_3820_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_val_3485_);
lean_dec(v_a_3481_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3820_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_fst_3489_; lean_object* v_snd_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3819_; 
v_fst_3489_ = lean_ctor_get(v_val_3485_, 0);
v_snd_3490_ = lean_ctor_get(v_val_3485_, 1);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_val_3485_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3492_ = v_val_3485_;
v_isShared_3493_ = v_isSharedCheck_3819_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_snd_3490_);
lean_inc(v_fst_3489_);
lean_dec(v_val_3485_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3819_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_Meta_saveState___redArg(v_a_3429_, v_a_3431_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3496_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref(v___x_3494_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_fst_3475_);
lean_inc(v_fst_3489_);
v___x_3496_ = l_Lean_Meta_isExprDefEq(v_fst_3489_, v_fst_3475_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3802_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3802_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3802_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
uint8_t v___x_3501_; 
v___x_3501_ = lean_unbox(v_a_3497_);
lean_dec(v_a_3497_);
if (v___x_3501_ == 0)
{
lean_object* v_options_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
lean_dec(v_a_3495_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3457_);
v_options_3502_ = lean_ctor_get(v_a_3430_, 2);
v___x_3503_ = l_Lean_Meta_autoLift;
v___x_3504_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_options_3502_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v___x_3505_ = lean_box(0);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3505_);
v___x_3507_ = v___x_3499_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
else
{
lean_object* v___x_3509_; 
lean_del_object(v___x_3499_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_fst_3489_);
v___x_3509_ = lean_infer_type(v_fst_3489_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3511_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref(v___x_3509_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3511_ = lean_whnf(v_a_3510_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref(v___x_3511_);
if (lean_obj_tag(v_a_3512_) == 7)
{
lean_object* v_binderType_3513_; 
v_binderType_3513_ = lean_ctor_get(v_a_3512_, 1);
if (lean_obj_tag(v_binderType_3513_) == 3)
{
lean_object* v_body_3514_; 
v_body_3514_ = lean_ctor_get(v_a_3512_, 2);
if (lean_obj_tag(v_body_3514_) == 3)
{
lean_object* v_u_3515_; lean_object* v_u_3516_; lean_object* v___x_3517_; 
lean_inc_ref(v_body_3514_);
lean_inc_ref(v_binderType_3513_);
lean_dec_ref(v_a_3512_);
v_u_3515_ = lean_ctor_get(v_binderType_3513_, 0);
lean_inc(v_u_3515_);
lean_dec_ref(v_binderType_3513_);
v_u_3516_ = lean_ctor_get(v_body_3514_, 0);
lean_inc(v_u_3516_);
lean_dec_ref(v_body_3514_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_fst_3475_);
v___x_3517_ = lean_infer_type(v_fst_3475_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref(v___x_3517_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3519_ = lean_whnf(v_a_3518_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref(v___x_3519_);
if (lean_obj_tag(v_a_3520_) == 7)
{
lean_object* v_binderType_3521_; 
v_binderType_3521_ = lean_ctor_get(v_a_3520_, 1);
if (lean_obj_tag(v_binderType_3521_) == 3)
{
lean_object* v_body_3522_; 
v_body_3522_ = lean_ctor_get(v_a_3520_, 2);
if (lean_obj_tag(v_body_3522_) == 3)
{
lean_object* v_u_3523_; lean_object* v_u_3524_; lean_object* v___x_3525_; 
lean_inc_ref(v_body_3522_);
lean_inc_ref(v_binderType_3521_);
lean_dec_ref(v_a_3520_);
v_u_3523_ = lean_ctor_get(v_binderType_3521_, 0);
lean_inc(v_u_3523_);
lean_dec_ref(v_binderType_3521_);
v_u_3524_ = lean_ctor_get(v_body_3522_, 0);
lean_inc(v_u_3524_);
lean_dec_ref(v_body_3522_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3525_ = l_Lean_Meta_decLevel(v_u_3515_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3527_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref(v___x_3525_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3527_ = l_Lean_Meta_decLevel(v_u_3523_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___x_3529_; 
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3528_);
lean_dec_ref(v___x_3527_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_a_3526_);
v___x_3529_ = l_Lean_Meta_isLevelDefEq(v_a_3526_, v_a_3528_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3694_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3532_ = v___x_3529_;
v_isShared_3533_ = v_isSharedCheck_3694_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3529_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3694_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
uint8_t v___x_3534_; 
v___x_3534_ = lean_unbox(v_a_3530_);
lean_dec(v_a_3530_);
if (v___x_3534_ == 1)
{
lean_object* v___x_3535_; 
lean_del_object(v___x_3532_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3535_ = l_Lean_Meta_decLevel(v_u_3516_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3537_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref(v___x_3535_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3537_ = l_Lean_Meta_decLevel(v_u_3524_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3542_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref(v___x_3537_);
v___x_3539_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3540_ = lean_box(0);
if (v_isShared_3493_ == 0)
{
lean_ctor_set_tag(v___x_3492_, 1);
lean_ctor_set(v___x_3492_, 1, v___x_3540_);
lean_ctor_set(v___x_3492_, 0, v_a_3538_);
v___x_3542_ = v___x_3492_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3538_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3544_; 
if (v_isShared_3479_ == 0)
{
lean_ctor_set_tag(v___x_3478_, 1);
lean_ctor_set(v___x_3478_, 1, v___x_3542_);
lean_ctor_set(v___x_3478_, 0, v_a_3536_);
v___x_3544_ = v___x_3478_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3536_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3545_, 0, v_a_3526_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = l_Lean_Expr_const___override(v___x_3539_, v___x_3545_);
v___x_3547_ = lean_unsigned_to_nat(2u);
v___x_3548_ = lean_mk_empty_array_with_capacity(v___x_3547_);
lean_inc(v_fst_3489_);
v___x_3549_ = lean_array_push(v___x_3548_, v_fst_3489_);
lean_inc(v_fst_3475_);
v___x_3550_ = lean_array_push(v___x_3549_, v_fst_3475_);
v___x_3551_ = l_Lean_mkAppN(v___x_3546_, v___x_3550_);
lean_dec_ref(v___x_3550_);
v___x_3552_ = lean_box(0);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3553_ = l_Lean_Meta_trySynthInstance(v___x_3551_, v___x_3552_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3684_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3684_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3684_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
if (lean_obj_tag(v_a_3554_) == 1)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; 
lean_del_object(v___x_3556_);
v_a_3558_ = lean_ctor_get(v_a_3554_, 0);
lean_inc(v_a_3558_);
lean_dec_ref(v_a_3554_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_snd_3490_);
v___x_3559_ = l_Lean_Meta_getDecLevel(v_snd_3490_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3561_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref(v___x_3559_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3561_ = l_Lean_Meta_getDecLevel(v_a_3462_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3563_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref(v___x_3561_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_a_3455_);
v___x_3563_ = l_Lean_Meta_getDecLevel(v_a_3455_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref(v___x_3563_);
v___x_3565_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3566_, 0, v_a_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3540_);
v___x_3567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3567_, 0, v_a_3562_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3568_, 0, v_a_3560_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
lean_inc_ref(v___x_3568_);
v___x_3569_ = l_Lean_mkConst(v___x_3565_, v___x_3568_);
v___x_3570_ = lean_unsigned_to_nat(5u);
v___x_3571_ = lean_mk_empty_array_with_capacity(v___x_3570_);
lean_inc(v_fst_3489_);
v___x_3572_ = lean_array_push(v___x_3571_, v_fst_3489_);
lean_inc(v_fst_3475_);
v___x_3573_ = lean_array_push(v___x_3572_, v_fst_3475_);
lean_inc(v_a_3558_);
v___x_3574_ = lean_array_push(v___x_3573_, v_a_3558_);
lean_inc(v_snd_3490_);
v___x_3575_ = lean_array_push(v___x_3574_, v_snd_3490_);
lean_inc_ref(v_e_3426_);
v___x_3576_ = lean_array_push(v___x_3575_, v_e_3426_);
v___x_3577_ = l_Lean_mkAppN(v___x_3569_, v___x_3576_);
lean_dec_ref(v___x_3576_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc_ref(v___x_3577_);
v___x_3578_ = lean_infer_type(v___x_3577_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3580_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_a_3579_);
lean_dec_ref(v___x_3578_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_a_3455_);
v___x_3580_ = l_Lean_Meta_isExprDefEq(v_a_3455_, v_a_3579_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3675_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3583_ = v___x_3580_;
v_isShared_3584_ = v_isSharedCheck_3675_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3580_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3675_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
uint8_t v___x_3585_; 
v___x_3585_ = lean_unbox(v_a_3581_);
lean_dec(v_a_3581_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3586_; 
lean_del_object(v___x_3583_);
lean_dec_ref(v___x_3577_);
lean_del_object(v___x_3487_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_fst_3475_);
v___x_3586_ = l_Lean_Meta_isMonad_x3f(v_fst_3475_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3667_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3589_ = v___x_3586_;
v_isShared_3590_ = v_isSharedCheck_3667_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3586_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3667_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
if (lean_obj_tag(v_a_3587_) == 1)
{
lean_object* v_val_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3663_; 
lean_del_object(v___x_3589_);
v_val_3591_ = lean_ctor_get(v_a_3587_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_a_3587_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3593_ = v_a_3587_;
v_isShared_3594_ = v_isSharedCheck_3663_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_val_3591_);
lean_dec(v_a_3587_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3663_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3595_; 
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_snd_3490_);
v___x_3595_ = l_Lean_Meta_getLevel(v_snd_3490_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3597_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___x_3595_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_snd_3476_);
v___x_3597_ = l_Lean_Meta_getLevel(v_snd_3476_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref(v___x_3597_);
v___x_3599_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3600_ = 0;
v___x_3601_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3602_, 0, v_a_3598_);
lean_ctor_set(v___x_3602_, 1, v___x_3540_);
v___x_3603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3603_, 0, v_a_3596_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = l_Lean_mkConst(v___x_3601_, v___x_3603_);
v___x_3605_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3606_ = lean_unsigned_to_nat(3u);
v___x_3607_ = lean_mk_empty_array_with_capacity(v___x_3606_);
lean_inc(v_snd_3490_);
v___x_3608_ = lean_array_push(v___x_3607_, v_snd_3490_);
v___x_3609_ = lean_array_push(v___x_3608_, v___x_3605_);
lean_inc(v_snd_3476_);
v___x_3610_ = lean_array_push(v___x_3609_, v_snd_3476_);
v___x_3611_ = l_Lean_mkAppN(v___x_3604_, v___x_3610_);
lean_dec_ref(v___x_3610_);
lean_inc(v_snd_3490_);
v___x_3612_ = l_Lean_mkForall(v___x_3599_, v___x_3600_, v_snd_3490_, v___x_3611_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3613_ = l_Lean_Meta_trySynthInstance(v___x_3612_, v___x_3552_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3659_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3616_ = v___x_3613_;
v_isShared_3617_ = v_isSharedCheck_3659_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3613_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3659_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
if (lean_obj_tag(v_a_3614_) == 1)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_del_object(v___x_3616_);
v_a_3618_ = lean_ctor_get(v_a_3614_, 0);
lean_inc(v_a_3618_);
lean_dec_ref(v_a_3614_);
v___x_3619_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3620_ = l_Lean_mkConst(v___x_3619_, v___x_3568_);
v___x_3621_ = lean_unsigned_to_nat(8u);
v___x_3622_ = lean_mk_empty_array_with_capacity(v___x_3621_);
v___x_3623_ = lean_array_push(v___x_3622_, v_fst_3489_);
v___x_3624_ = lean_array_push(v___x_3623_, v_fst_3475_);
v___x_3625_ = lean_array_push(v___x_3624_, v_snd_3490_);
v___x_3626_ = lean_array_push(v___x_3625_, v_snd_3476_);
v___x_3627_ = lean_array_push(v___x_3626_, v_a_3558_);
v___x_3628_ = lean_array_push(v___x_3627_, v_a_3618_);
v___x_3629_ = lean_array_push(v___x_3628_, v_val_3591_);
v___x_3630_ = lean_array_push(v___x_3629_, v_e_3426_);
v___x_3631_ = l_Lean_mkAppN(v___x_3620_, v___x_3630_);
lean_dec_ref(v___x_3630_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3632_ = l_Lean_Meta_expandCoe(v___x_3631_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v_fst_3634_; lean_object* v___x_3635_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref(v___x_3632_);
v_fst_3634_ = lean_ctor_get(v_a_3633_, 0);
lean_inc(v_fst_3634_);
lean_dec(v_a_3633_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_fst_3634_);
v___x_3635_ = lean_infer_type(v_fst_3634_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v___x_3637_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3636_);
lean_dec_ref(v___x_3635_);
v___x_3637_ = l_Lean_Meta_isExprDefEq(v_a_3455_, v_a_3636_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3652_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3640_ = v___x_3637_;
v_isShared_3641_ = v_isSharedCheck_3652_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3652_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
uint8_t v___x_3642_; 
v___x_3642_ = lean_unbox(v_a_3638_);
lean_dec(v_a_3638_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3644_; 
lean_dec(v_fst_3634_);
lean_del_object(v___x_3593_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3552_);
v___x_3644_ = v___x_3640_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3552_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
else
{
lean_object* v___x_3647_; 
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v_fst_3634_);
v___x_3647_ = v___x_3593_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_fst_3634_);
v___x_3647_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3649_; 
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3647_);
v___x_3649_ = v___x_3640_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
else
{
lean_object* v_a_3653_; 
lean_dec(v_fst_3634_);
lean_del_object(v___x_3593_);
v_a_3653_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3653_);
lean_dec_ref(v___x_3637_);
v_a_3440_ = v_a_3653_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3654_; 
lean_dec(v_fst_3634_);
lean_del_object(v___x_3593_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
v_a_3654_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3654_);
lean_dec_ref(v___x_3635_);
v_a_3440_ = v_a_3654_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3655_; 
lean_del_object(v___x_3593_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
v_a_3655_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3655_);
lean_dec_ref(v___x_3632_);
v_a_3440_ = v_a_3655_;
goto v___jp_3439_;
}
}
else
{
lean_object* v___x_3657_; 
lean_dec(v_a_3614_);
lean_del_object(v___x_3593_);
lean_dec(v_val_3591_);
lean_dec_ref(v___x_3568_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3552_);
v___x_3657_ = v___x_3616_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3552_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
else
{
lean_object* v_a_3660_; 
lean_del_object(v___x_3593_);
lean_dec(v_val_3591_);
lean_dec_ref(v___x_3568_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3660_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3660_);
lean_dec_ref(v___x_3613_);
v_a_3440_ = v_a_3660_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3661_; 
lean_dec(v_a_3596_);
lean_del_object(v___x_3593_);
lean_dec(v_val_3591_);
lean_dec_ref(v___x_3568_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3661_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3661_);
lean_dec_ref(v___x_3597_);
v_a_3440_ = v_a_3661_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3662_; 
lean_del_object(v___x_3593_);
lean_dec(v_val_3591_);
lean_dec_ref(v___x_3568_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3662_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3595_);
v_a_3440_ = v_a_3662_;
goto v___jp_3439_;
}
}
}
else
{
lean_object* v___x_3665_; 
lean_dec(v_a_3587_);
lean_dec_ref(v___x_3568_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v___x_3552_);
v___x_3665_ = v___x_3589_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3552_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_a_3668_; 
lean_dec_ref(v___x_3568_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3668_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3668_);
lean_dec_ref(v___x_3586_);
v_a_3440_ = v_a_3668_;
goto v___jp_3439_;
}
}
else
{
lean_object* v___x_3670_; 
lean_dec_ref(v___x_3568_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v___x_3577_);
v___x_3670_ = v___x_3487_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3577_);
v___x_3670_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3672_; 
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3670_);
v___x_3672_ = v___x_3583_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
else
{
lean_object* v_a_3676_; 
lean_dec_ref(v___x_3577_);
lean_dec_ref(v___x_3568_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3676_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3676_);
lean_dec_ref(v___x_3580_);
v_a_3440_ = v_a_3676_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3677_; 
lean_dec_ref(v___x_3577_);
lean_dec_ref(v___x_3568_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3677_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_a_3677_);
lean_dec_ref(v___x_3578_);
v_a_3440_ = v_a_3677_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3678_; 
lean_dec(v_a_3562_);
lean_dec(v_a_3560_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3678_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3678_);
lean_dec_ref(v___x_3563_);
v_a_3440_ = v_a_3678_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3679_; 
lean_dec(v_a_3560_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3679_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3679_);
lean_dec_ref(v___x_3561_);
v_a_3440_ = v_a_3679_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3680_; 
lean_dec(v_a_3558_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3680_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3680_);
lean_dec_ref(v___x_3559_);
v_a_3440_ = v_a_3680_;
goto v___jp_3439_;
}
}
else
{
lean_object* v___x_3682_; 
lean_dec(v_a_3554_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v___x_3552_);
v___x_3682_ = v___x_3556_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3552_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_object* v_a_3685_; 
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3685_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3685_);
lean_dec_ref(v___x_3553_);
v_a_3440_ = v_a_3685_;
goto v___jp_3439_;
}
}
}
}
else
{
lean_object* v_a_3688_; 
lean_dec(v_a_3536_);
lean_dec(v_a_3526_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3688_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3688_);
lean_dec_ref(v___x_3537_);
v_a_3440_ = v_a_3688_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3689_; 
lean_dec(v_a_3526_);
lean_dec(v_u_3524_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3689_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3689_);
lean_dec_ref(v___x_3535_);
v_a_3440_ = v_a_3689_;
goto v___jp_3439_;
}
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3692_; 
lean_dec(v_a_3526_);
lean_dec(v_u_3524_);
lean_dec(v_u_3516_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v___x_3690_ = lean_box(0);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v___x_3690_);
v___x_3692_ = v___x_3532_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
else
{
lean_object* v_a_3695_; 
lean_dec(v_a_3526_);
lean_dec(v_u_3524_);
lean_dec(v_u_3516_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3695_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3695_);
lean_dec_ref(v___x_3529_);
v_a_3440_ = v_a_3695_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3696_; 
lean_dec(v_a_3526_);
lean_dec(v_u_3524_);
lean_dec(v_u_3516_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3696_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3696_);
lean_dec_ref(v___x_3527_);
v_a_3440_ = v_a_3696_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3697_; 
lean_dec(v_u_3524_);
lean_dec(v_u_3523_);
lean_dec(v_u_3516_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3697_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3697_);
lean_dec_ref(v___x_3525_);
v_a_3440_ = v_a_3697_;
goto v___jp_3439_;
}
}
else
{
lean_object* v___x_3698_; 
lean_dec(v_u_3516_);
lean_dec(v_u_3515_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec_ref(v_e_3426_);
v___x_3698_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3520_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_a_3520_);
v___y_3444_ = v___x_3698_;
goto v___jp_3443_;
}
}
else
{
lean_object* v___x_3699_; 
lean_dec(v_u_3516_);
lean_dec(v_u_3515_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec_ref(v_e_3426_);
v___x_3699_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3520_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_a_3520_);
v___y_3444_ = v___x_3699_;
goto v___jp_3443_;
}
}
else
{
lean_object* v___x_3700_; 
lean_dec(v_u_3516_);
lean_dec(v_u_3515_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec_ref(v_e_3426_);
v___x_3700_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3520_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec(v_a_3520_);
v___y_3444_ = v___x_3700_;
goto v___jp_3443_;
}
}
else
{
lean_object* v_a_3701_; 
lean_dec(v_u_3516_);
lean_dec(v_u_3515_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3701_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3701_);
lean_dec_ref(v___x_3519_);
v_a_3440_ = v_a_3701_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3702_; 
lean_dec(v_u_3516_);
lean_dec(v_u_3515_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3702_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3702_);
lean_dec_ref(v___x_3517_);
v_a_3440_ = v_a_3702_;
goto v___jp_3439_;
}
}
else
{
lean_object* v___x_3703_; 
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec_ref(v_e_3426_);
v___x_3703_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3512_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_a_3512_);
v___y_3444_ = v___x_3703_;
goto v___jp_3443_;
}
}
else
{
lean_object* v___x_3704_; 
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec_ref(v_e_3426_);
v___x_3704_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3512_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_a_3512_);
v___y_3444_ = v___x_3704_;
goto v___jp_3443_;
}
}
else
{
lean_object* v___x_3705_; 
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec_ref(v_e_3426_);
v___x_3705_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3512_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec(v_a_3512_);
v___y_3444_ = v___x_3705_;
goto v___jp_3443_;
}
}
else
{
lean_object* v_a_3706_; 
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3706_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3706_);
lean_dec_ref(v___x_3511_);
v_a_3440_ = v_a_3706_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3707_; 
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3707_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3707_);
lean_dec_ref(v___x_3509_);
v_a_3440_ = v_a_3707_;
goto v___jp_3439_;
}
}
}
else
{
lean_object* v___x_3708_; 
lean_del_object(v___x_3499_);
lean_del_object(v___x_3492_);
lean_del_object(v___x_3478_);
lean_dec(v_a_3462_);
lean_dec(v_a_3455_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3708_ = l_Lean_Meta_isMonad_x3f(v_fst_3475_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3801_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3711_ = v___x_3708_;
v_isShared_3712_ = v_isSharedCheck_3801_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3801_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
if (lean_obj_tag(v_a_3709_) == 1)
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
v___x_3713_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v_fst_3489_);
v___x_3715_ = v___x_3487_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_fst_3489_);
v___x_3715_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3717_; 
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v_snd_3490_);
v___x_3717_ = v___x_3473_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_snd_3490_);
v___x_3717_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3719_; 
if (v_isShared_3465_ == 0)
{
lean_ctor_set_tag(v___x_3464_, 1);
lean_ctor_set(v___x_3464_, 0, v_snd_3476_);
v___x_3719_ = v___x_3464_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_snd_3476_);
v___x_3719_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3720_; lean_object* v___y_3722_; uint8_t v___y_3723_; lean_object* v_a_3745_; lean_object* v___x_3749_; 
v___x_3720_ = lean_box(0);
if (v_isShared_3458_ == 0)
{
lean_ctor_set_tag(v___x_3457_, 1);
lean_ctor_set(v___x_3457_, 0, v_e_3426_);
v___x_3749_ = v___x_3457_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_e_3426_);
v___x_3749_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3748_;
}
v___jp_3721_:
{
if (v___y_3723_ == 0)
{
lean_object* v___x_3724_; 
lean_dec_ref(v___y_3722_);
lean_del_object(v___x_3711_);
v___x_3724_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3495_, v_a_3429_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec(v_a_3429_);
lean_dec(v_a_3495_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; 
v_unused_3732_ = lean_ctor_get(v___x_3724_, 0);
lean_dec(v_unused_3732_);
v___x_3726_ = v___x_3724_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_dec(v___x_3724_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v___x_3720_);
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3720_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
v_a_3733_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3724_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3724_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v___x_3742_; 
lean_dec(v_a_3495_);
lean_dec(v_a_3431_);
lean_dec(v_a_3429_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set_tag(v___x_3711_, 1);
lean_ctor_set(v___x_3711_, 0, v___y_3722_);
v___x_3742_ = v___x_3711_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___y_3722_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
v___jp_3744_:
{
uint8_t v___x_3746_; 
v___x_3746_ = l_Lean_Exception_isInterrupt(v_a_3745_);
if (v___x_3746_ == 0)
{
uint8_t v___x_3747_; 
lean_inc_ref(v_a_3745_);
v___x_3747_ = l_Lean_Exception_isRuntime(v_a_3745_);
v___y_3722_ = v_a_3745_;
v___y_3723_ = v___x_3747_;
goto v___jp_3721_;
}
else
{
v___y_3722_ = v_a_3745_;
v___y_3723_ = v___x_3746_;
goto v___jp_3721_;
}
}
v_reusejp_3748_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3750_ = lean_unsigned_to_nat(6u);
v___x_3751_ = lean_mk_empty_array_with_capacity(v___x_3750_);
v___x_3752_ = lean_array_push(v___x_3751_, v___x_3715_);
v___x_3753_ = lean_array_push(v___x_3752_, v___x_3717_);
v___x_3754_ = lean_array_push(v___x_3753_, v___x_3719_);
v___x_3755_ = lean_array_push(v___x_3754_, v___x_3720_);
v___x_3756_ = lean_array_push(v___x_3755_, v_a_3709_);
v___x_3757_ = lean_array_push(v___x_3756_, v___x_3749_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
v___x_3758_ = l_Lean_Meta_mkAppOptM(v___x_3713_, v___x_3757_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3777_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3761_ = v___x_3758_;
v_isShared_3762_ = v_isSharedCheck_3777_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3758_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3777_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3763_; 
lean_inc(v_a_3431_);
lean_inc(v_a_3429_);
v___x_3763_ = l_Lean_Meta_expandCoe(v_a_3759_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3775_; 
lean_del_object(v___x_3711_);
lean_dec(v_a_3495_);
lean_dec(v_a_3431_);
lean_dec(v_a_3429_);
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3766_ = v___x_3763_;
v_isShared_3767_ = v_isSharedCheck_3775_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3763_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3775_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v_fst_3768_; lean_object* v___x_3770_; 
v_fst_3768_ = lean_ctor_get(v_a_3764_, 0);
lean_inc(v_fst_3768_);
lean_dec(v_a_3764_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set_tag(v___x_3761_, 1);
lean_ctor_set(v___x_3761_, 0, v_fst_3768_);
v___x_3770_ = v___x_3761_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_fst_3768_);
v___x_3770_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3772_; 
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 0, v___x_3770_);
v___x_3772_ = v___x_3766_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_a_3776_; 
lean_del_object(v___x_3761_);
v_a_3776_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3776_);
lean_dec_ref(v___x_3763_);
v_a_3745_ = v_a_3776_;
goto v___jp_3744_;
}
}
}
else
{
lean_object* v_a_3778_; 
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_a_3428_);
v_a_3778_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3778_);
lean_dec_ref(v___x_3758_);
v_a_3745_ = v_a_3778_;
goto v___jp_3744_;
}
}
}
}
}
}
else
{
lean_object* v___x_3783_; 
lean_del_object(v___x_3711_);
lean_dec(v_a_3709_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3476_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3457_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v___x_3783_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3495_, v_a_3429_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec(v_a_3429_);
lean_dec(v_a_3495_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3791_; 
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; 
v_unused_3792_ = lean_ctor_get(v___x_3783_, 0);
lean_dec(v_unused_3792_);
v___x_3785_ = v___x_3783_;
v_isShared_3786_ = v_isSharedCheck_3791_;
goto v_resetjp_3784_;
}
else
{
lean_dec(v___x_3783_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3791_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3787_ = lean_box(0);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v___x_3787_);
v___x_3789_ = v___x_3785_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
v_a_3793_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3783_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3783_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
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
}
else
{
lean_dec(v_a_3495_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3476_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3457_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
return v___x_3708_;
}
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec(v_a_3495_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_a_3462_);
lean_del_object(v___x_3457_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3803_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3496_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3496_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
lean_del_object(v___x_3487_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_a_3462_);
lean_del_object(v___x_3457_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3811_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3494_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3494_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
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
}
}
else
{
lean_object* v___x_3821_; lean_object* v___x_3823_; 
lean_dec(v_a_3481_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_a_3462_);
lean_del_object(v___x_3457_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v___x_3821_ = lean_box(0);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3821_);
v___x_3823_ = v___x_3483_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
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
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_a_3462_);
lean_del_object(v___x_3457_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3826_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3480_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3480_);
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
lean_object* v___x_3836_; lean_object* v___x_3838_; 
lean_dec(v_a_3467_);
lean_del_object(v___x_3464_);
lean_dec(v_a_3462_);
lean_del_object(v___x_3457_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v___x_3836_ = lean_box(0);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3836_);
v___x_3838_ = v___x_3469_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_del_object(v___x_3464_);
lean_dec(v_a_3462_);
lean_del_object(v___x_3457_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3841_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3466_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3466_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_del_object(v___x_3457_);
lean_dec(v_a_3455_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3426_);
v_a_3850_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3459_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3459_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3859_, lean_object* v_expectedType_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3859_, v_expectedType_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3867_, lean_object* v_expectedType_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v___x_3874_; 
lean_inc(v_a_3872_);
lean_inc_ref(v_a_3871_);
lean_inc(v_a_3870_);
lean_inc_ref(v_a_3869_);
lean_inc_ref(v_expectedType_3868_);
lean_inc_ref(v_expr_3867_);
v___x_3874_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3867_, v_expectedType_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3954_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3954_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3954_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
if (lean_obj_tag(v_a_3875_) == 1)
{
lean_object* v_val_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3891_; 
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec_ref(v_expectedType_3868_);
lean_dec_ref(v_expr_3867_);
v_val_3879_ = lean_ctor_get(v_a_3875_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_a_3875_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3881_ = v_a_3875_;
v_isShared_3882_ = v_isSharedCheck_3891_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_val_3879_);
lean_dec(v_a_3875_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3891_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3883_ = lean_box(0);
v___x_3884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3884_, 0, v_val_3879_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v___x_3884_);
v___x_3886_ = v___x_3881_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3888_; 
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v___x_3886_);
v___x_3888_ = v___x_3877_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
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
else
{
lean_object* v___x_3892_; 
lean_del_object(v___x_3877_);
lean_dec(v_a_3875_);
lean_inc(v_a_3872_);
lean_inc_ref(v_a_3871_);
lean_inc(v_a_3870_);
lean_inc_ref(v_a_3869_);
lean_inc_ref(v_expectedType_3868_);
v___x_3892_ = l_Lean_Meta_whnfR(v_expectedType_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; uint8_t v___x_3894_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref(v___x_3892_);
v___x_3894_ = l_Lean_Expr_isForall(v_a_3893_);
lean_dec(v_a_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; 
v___x_3895_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3867_, v_expectedType_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
return v___x_3895_;
}
else
{
lean_object* v___x_3896_; 
lean_inc(v_a_3872_);
lean_inc_ref(v_a_3871_);
lean_inc(v_a_3870_);
lean_inc_ref(v_a_3869_);
lean_inc_ref(v_expr_3867_);
v___x_3896_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3867_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref(v___x_3896_);
if (lean_obj_tag(v_a_3897_) == 1)
{
lean_object* v_val_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3936_; 
v_val_3898_ = lean_ctor_get(v_a_3897_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_a_3897_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3900_ = v_a_3897_;
v_isShared_3901_ = v_isSharedCheck_3936_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_val_3898_);
lean_dec(v_a_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3936_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; 
lean_inc(v_a_3872_);
lean_inc_ref(v_a_3871_);
lean_inc(v_a_3870_);
lean_inc_ref(v_a_3869_);
lean_inc(v_val_3898_);
v___x_3902_ = lean_infer_type(v_val_3898_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3904_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref(v___x_3902_);
lean_inc(v_a_3872_);
lean_inc_ref(v_a_3871_);
lean_inc(v_a_3870_);
lean_inc_ref(v_a_3869_);
lean_inc_ref(v_expectedType_3868_);
v___x_3904_ = l_Lean_Meta_isExprDefEq(v_a_3903_, v_expectedType_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3919_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3919_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3919_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
uint8_t v___x_3909_; 
v___x_3909_ = lean_unbox(v_a_3905_);
lean_dec(v_a_3905_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; 
lean_del_object(v___x_3907_);
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
v___x_3910_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3867_, v_expectedType_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
return v___x_3910_;
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3914_; 
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec_ref(v_expectedType_3868_);
lean_dec_ref(v_expr_3867_);
v___x_3911_ = lean_box(0);
v___x_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3912_, 0, v_val_3898_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3912_);
v___x_3914_ = v___x_3900_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3916_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3914_);
v___x_3916_ = v___x_3907_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec_ref(v_expectedType_3868_);
lean_dec_ref(v_expr_3867_);
v_a_3920_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3904_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3904_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec_ref(v_expectedType_3868_);
lean_dec_ref(v_expr_3867_);
v_a_3928_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3902_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3902_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
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
}
else
{
lean_object* v___x_3937_; 
lean_dec(v_a_3897_);
v___x_3937_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3867_, v_expectedType_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
return v___x_3937_;
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec_ref(v_expectedType_3868_);
lean_dec_ref(v_expr_3867_);
v_a_3938_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3896_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3896_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
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
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec_ref(v_expectedType_3868_);
lean_dec_ref(v_expr_3867_);
v_a_3946_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3892_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3892_);
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
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec_ref(v_expectedType_3868_);
lean_dec_ref(v_expr_3867_);
v_a_3955_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3874_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3874_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3963_, lean_object* v_expectedType_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3963_, v_expectedType_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3971_, lean_object* v_expectedType_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3971_, v_expectedType_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_4003_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3981_ = v___x_3978_;
v_isShared_3982_ = v_isSharedCheck_4003_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3978_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_4003_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
switch(lean_obj_tag(v_a_3979_))
{
case 0:
{
lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3983_ = lean_box(0);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v___x_3983_);
v___x_3985_ = v___x_3981_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
case 1:
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3998_; 
v_a_3987_ = lean_ctor_get(v_a_3979_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_a_3979_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3989_ = v_a_3979_;
v_isShared_3990_ = v_isSharedCheck_3998_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v_a_3979_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3998_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v_fst_3991_; lean_object* v___x_3993_; 
v_fst_3991_ = lean_ctor_get(v_a_3987_, 0);
lean_inc(v_fst_3991_);
lean_dec(v_a_3987_);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v_fst_3991_);
v___x_3993_ = v___x_3989_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_fst_3991_);
v___x_3993_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3995_; 
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v___x_3993_);
v___x_3995_ = v___x_3981_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
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
default: 
{
lean_object* v___x_3999_; lean_object* v___x_4001_; 
v___x_3999_ = lean_box(2);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v___x_3999_);
v___x_4001_ = v___x_3981_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
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
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
v_a_4004_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3978_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3978_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_4012_, lean_object* v_expectedType_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Lean_Meta_coerce_x3f(v_expr_4012_, v_expectedType_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_);
return v_res_4019_;
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
