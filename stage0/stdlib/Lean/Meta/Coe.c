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
size_t v_x_37475__boxed_307_; uint8_t v_res_308_; lean_object* v_r_309_; 
v_x_37475__boxed_307_ = lean_unbox_usize(v_x_305_);
lean_dec(v_x_305_);
v_res_308_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_304_, v_x_37475__boxed_307_, v_x_306_);
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
lean_object* v___y_1042_; lean_object* v_fileName_1059_; lean_object* v_fileMap_1060_; lean_object* v_options_1061_; lean_object* v_currRecDepth_1062_; lean_object* v_maxRecDepth_1063_; lean_object* v_ref_1064_; lean_object* v_currNamespace_1065_; lean_object* v_openDecls_1066_; lean_object* v_initHeartbeats_1067_; lean_object* v_maxHeartbeats_1068_; lean_object* v_quotContext_1069_; lean_object* v_currMacroScope_1070_; uint8_t v_diag_1071_; lean_object* v_cancelTk_x3f_1072_; uint8_t v_suppressElabErrors_1073_; lean_object* v_inheritedTraceOptions_1074_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
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
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_nat_dec_eq(v_maxRecDepth_1063_, v___x_1080_);
if (v___x_1081_ == 0)
{
uint8_t v___x_1082_; 
v___x_1082_ = lean_nat_dec_eq(v_currRecDepth_1062_, v_maxRecDepth_1063_);
if (v___x_1082_ == 0)
{
goto v___jp_1075_;
}
else
{
lean_object* v___x_1083_; 
lean_dec(v___y_1035_);
lean_dec_ref(v_x_1033_);
lean_inc(v_ref_1064_);
v___x_1083_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1064_);
v___y_1042_ = v___x_1083_;
goto v___jp_1041_;
}
}
else
{
goto v___jp_1075_;
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
v___jp_1075_:
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1085_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(lean_object* v_a_1093_, lean_object* v_x_1094_){
_start:
{
if (lean_obj_tag(v_x_1094_) == 0)
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_box(0);
return v___x_1095_;
}
else
{
lean_object* v_key_1096_; lean_object* v_value_1097_; lean_object* v_tail_1098_; uint8_t v___x_1099_; 
v_key_1096_ = lean_ctor_get(v_x_1094_, 0);
v_value_1097_ = lean_ctor_get(v_x_1094_, 1);
v_tail_1098_ = lean_ctor_get(v_x_1094_, 2);
v___x_1099_ = l_Lean_ExprStructEq_beq(v_key_1096_, v_a_1093_);
if (v___x_1099_ == 0)
{
v_x_1094_ = v_tail_1098_;
goto _start;
}
else
{
lean_object* v___x_1101_; 
lean_inc(v_value_1097_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_value_1097_);
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(lean_object* v_a_1102_, lean_object* v_x_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1102_, v_x_1103_);
lean_dec(v_x_1103_);
lean_dec_ref(v_a_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_m_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_buckets_1107_; lean_object* v___x_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; uint64_t v___x_1111_; uint64_t v_fold_1112_; uint64_t v___x_1113_; uint64_t v___x_1114_; uint64_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_buckets_1107_ = lean_ctor_get(v_m_1105_, 1);
v___x_1108_ = lean_array_get_size(v_buckets_1107_);
v___x_1109_ = l_Lean_ExprStructEq_hash(v_a_1106_);
v___x_1110_ = 32ULL;
v___x_1111_ = lean_uint64_shift_right(v___x_1109_, v___x_1110_);
v_fold_1112_ = lean_uint64_xor(v___x_1109_, v___x_1111_);
v___x_1113_ = 16ULL;
v___x_1114_ = lean_uint64_shift_right(v_fold_1112_, v___x_1113_);
v___x_1115_ = lean_uint64_xor(v_fold_1112_, v___x_1114_);
v___x_1116_ = lean_uint64_to_usize(v___x_1115_);
v___x_1117_ = lean_usize_of_nat(v___x_1108_);
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = lean_usize_sub(v___x_1117_, v___x_1118_);
v___x_1120_ = lean_usize_land(v___x_1116_, v___x_1119_);
v___x_1121_ = lean_array_uget_borrowed(v_buckets_1107_, v___x_1120_);
v___x_1122_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1106_, v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_m_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_1123_, v_a_1124_);
lean_dec_ref(v_a_1124_);
lean_dec_ref(v_m_1123_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1126_, lean_object* v_x_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_apply_1(v_x_1127_, lean_box(0));
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v___y_1128_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_x_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1137_, v_x_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1149_, lean_object* v_pre_1150_, lean_object* v_post_1151_, uint8_t v_usedLetOnly_1152_, uint8_t v_skipConstInApp_1153_, uint8_t v_skipInstances_1154_, lean_object* v_body_1155_, lean_object* v_x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_array_push(v_fvars_1149_, v_x_1156_);
v___x_1165_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1150_, v_post_1151_, v_usedLetOnly_1152_, v_skipConstInApp_1153_, v_skipInstances_1154_, v___x_1164_, v_body_1155_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1166_, lean_object* v_pre_1167_, lean_object* v_post_1168_, lean_object* v_usedLetOnly_1169_, lean_object* v_skipConstInApp_1170_, lean_object* v_skipInstances_1171_, lean_object* v_body_1172_, lean_object* v_x_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v_usedLetOnly_boxed_1181_; uint8_t v_skipConstInApp_boxed_1182_; uint8_t v_skipInstances_boxed_1183_; lean_object* v_res_1184_; 
v_usedLetOnly_boxed_1181_ = lean_unbox(v_usedLetOnly_1169_);
v_skipConstInApp_boxed_1182_ = lean_unbox(v_skipConstInApp_1170_);
v_skipInstances_boxed_1183_ = lean_unbox(v_skipInstances_1171_);
v_res_1184_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1166_, v_pre_1167_, v_post_1168_, v_usedLetOnly_boxed_1181_, v_skipConstInApp_boxed_1182_, v_skipInstances_boxed_1183_, v_body_1172_, v_x_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1174_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1185_, lean_object* v_post_1186_, uint8_t v_usedLetOnly_1187_, uint8_t v_skipConstInApp_1188_, uint8_t v_skipInstances_1189_, lean_object* v_e_1190_, lean_object* v_a_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; 
lean_inc_ref(v_post_1186_);
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1195_);
lean_inc(v___y_1194_);
lean_inc_ref(v___y_1193_);
lean_inc_ref(v_e_1190_);
v___x_1198_ = lean_apply_7(v_post_1186_, v_e_1190_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, lean_box(0));
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1230_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1230_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1230_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1229_; 
v_fst_1203_ = lean_ctor_get(v_a_1199_, 0);
v_snd_1204_ = lean_ctor_get(v_a_1199_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_a_1199_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1206_ = v_a_1199_;
v_isShared_1207_ = v_isSharedCheck_1229_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_snd_1204_);
lean_inc(v_fst_1203_);
lean_dec(v_a_1199_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1229_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___y_1209_; 
switch(lean_obj_tag(v_fst_1203_))
{
case 0:
{
lean_object* v_e_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1224_; 
lean_del_object(v___x_1206_);
lean_del_object(v___x_1201_);
lean_dec_ref(v_e_1190_);
lean_dec_ref(v_post_1186_);
lean_dec_ref(v_pre_1185_);
v_e_1216_ = lean_ctor_get(v_fst_1203_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_fst_1203_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1218_ = v_fst_1203_;
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_e_1216_);
lean_dec(v_fst_1203_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_e_1216_);
lean_ctor_set(v___x_1220_, 1, v_snd_1204_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
case 1:
{
lean_object* v_e_1225_; lean_object* v___x_1226_; 
lean_del_object(v___x_1206_);
lean_del_object(v___x_1201_);
lean_dec_ref(v_e_1190_);
v_e_1225_ = lean_ctor_get(v_fst_1203_, 0);
lean_inc_ref(v_e_1225_);
lean_dec_ref(v_fst_1203_);
v___x_1226_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1185_, v_post_1186_, v_usedLetOnly_1187_, v_skipConstInApp_1188_, v_skipInstances_1189_, v_e_1225_, v_a_1191_, v_snd_1204_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
return v___x_1226_;
}
default: 
{
lean_object* v_e_x3f_1227_; 
lean_dec_ref(v_post_1186_);
lean_dec_ref(v_pre_1185_);
v_e_x3f_1227_ = lean_ctor_get(v_fst_1203_, 0);
lean_inc(v_e_x3f_1227_);
lean_dec_ref(v_fst_1203_);
if (lean_obj_tag(v_e_x3f_1227_) == 0)
{
v___y_1209_ = v_e_1190_;
goto v___jp_1208_;
}
else
{
lean_object* v_val_1228_; 
lean_dec_ref(v_e_1190_);
v_val_1228_ = lean_ctor_get(v_e_x3f_1227_, 0);
lean_inc(v_val_1228_);
lean_dec_ref(v_e_x3f_1227_);
v___y_1209_ = v_val_1228_;
goto v___jp_1208_;
}
}
}
v___jp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___y_1209_);
v___x_1211_ = v___x_1206_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___y_1209_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_snd_1204_);
v___x_1211_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1213_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1211_);
v___x_1213_ = v___x_1201_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec_ref(v_e_1190_);
lean_dec_ref(v_post_1186_);
lean_dec_ref(v_pre_1185_);
v_a_1231_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1198_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1198_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1239_, lean_object* v_post_1240_, uint8_t v_usedLetOnly_1241_, uint8_t v_skipConstInApp_1242_, uint8_t v_skipInstances_1243_, lean_object* v_fvars_1244_, lean_object* v_e_1245_, lean_object* v_a_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
if (lean_obj_tag(v_e_1245_) == 6)
{
lean_object* v_binderName_1253_; lean_object* v_binderType_1254_; lean_object* v_body_1255_; uint8_t v_binderInfo_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_binderName_1253_ = lean_ctor_get(v_e_1245_, 0);
lean_inc(v_binderName_1253_);
v_binderType_1254_ = lean_ctor_get(v_e_1245_, 1);
lean_inc_ref(v_binderType_1254_);
v_body_1255_ = lean_ctor_get(v_e_1245_, 2);
lean_inc_ref(v_body_1255_);
v_binderInfo_1256_ = lean_ctor_get_uint8(v_e_1245_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1245_);
v___x_1257_ = lean_expr_instantiate_rev(v_binderType_1254_, v_fvars_1244_);
lean_dec_ref(v_binderType_1254_);
lean_inc_ref(v_post_1240_);
lean_inc_ref(v_pre_1239_);
v___x_1258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1239_, v_post_1240_, v_usedLetOnly_1241_, v_skipConstInApp_1242_, v_skipInstances_1243_, v___x_1257_, v_a_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v_fst_1260_; lean_object* v_snd_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___f_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
v_fst_1260_ = lean_ctor_get(v_a_1259_, 0);
lean_inc(v_fst_1260_);
v_snd_1261_ = lean_ctor_get(v_a_1259_, 1);
lean_inc(v_snd_1261_);
lean_dec(v_a_1259_);
v___x_1262_ = lean_box(v_usedLetOnly_1241_);
v___x_1263_ = lean_box(v_skipConstInApp_1242_);
v___x_1264_ = lean_box(v_skipInstances_1243_);
v___f_1265_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1265_, 0, v_fvars_1244_);
lean_closure_set(v___f_1265_, 1, v_pre_1239_);
lean_closure_set(v___f_1265_, 2, v_post_1240_);
lean_closure_set(v___f_1265_, 3, v___x_1262_);
lean_closure_set(v___f_1265_, 4, v___x_1263_);
lean_closure_set(v___f_1265_, 5, v___x_1264_);
lean_closure_set(v___f_1265_, 6, v_body_1255_);
v___x_1266_ = 0;
v___x_1267_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1253_, v_binderInfo_1256_, v_fst_1260_, v___f_1265_, v___x_1266_, v_a_1246_, v_snd_1261_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
return v___x_1267_;
}
else
{
lean_dec_ref(v_body_1255_);
lean_dec(v_binderName_1253_);
lean_dec_ref(v_fvars_1244_);
lean_dec_ref(v_post_1240_);
lean_dec_ref(v_pre_1239_);
return v___x_1258_;
}
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_expr_instantiate_rev(v_e_1245_, v_fvars_1244_);
lean_dec_ref(v_e_1245_);
lean_inc_ref(v_post_1240_);
lean_inc_ref(v_pre_1239_);
v___x_1269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1239_, v_post_1240_, v_usedLetOnly_1241_, v_skipConstInApp_1242_, v_skipInstances_1243_, v___x_1268_, v_a_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; uint8_t v___x_1273_; uint8_t v___x_1274_; uint8_t v___x_1275_; lean_object* v___x_1276_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
v_fst_1271_ = lean_ctor_get(v_a_1270_, 0);
lean_inc(v_fst_1271_);
v_snd_1272_ = lean_ctor_get(v_a_1270_, 1);
lean_inc(v_snd_1272_);
lean_dec(v_a_1270_);
v___x_1273_ = 0;
v___x_1274_ = 1;
v___x_1275_ = 1;
v___x_1276_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1244_, v_fst_1271_, v___x_1273_, v_usedLetOnly_1241_, v___x_1273_, v___x_1274_, v___x_1275_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec_ref(v_fvars_1244_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1239_, v_post_1240_, v_usedLetOnly_1241_, v_skipConstInApp_1242_, v_skipInstances_1243_, v_a_1277_, v_a_1246_, v_snd_1272_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
return v___x_1278_;
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec(v_snd_1272_);
lean_dec_ref(v_post_1240_);
lean_dec_ref(v_pre_1239_);
v_a_1279_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1276_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1276_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1244_);
lean_dec_ref(v_post_1240_);
lean_dec_ref(v_pre_1239_);
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1287_, lean_object* v_pre_1288_, lean_object* v_post_1289_, uint8_t v_usedLetOnly_1290_, uint8_t v_skipConstInApp_1291_, uint8_t v_skipInstances_1292_, lean_object* v_body_1293_, lean_object* v_x_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_array_push(v_fvars_1287_, v_x_1294_);
v___x_1303_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1288_, v_post_1289_, v_usedLetOnly_1290_, v_skipConstInApp_1291_, v_skipInstances_1292_, v___x_1302_, v_body_1293_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1304_, lean_object* v_pre_1305_, lean_object* v_post_1306_, lean_object* v_usedLetOnly_1307_, lean_object* v_skipConstInApp_1308_, lean_object* v_skipInstances_1309_, lean_object* v_body_1310_, lean_object* v_x_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v_usedLetOnly_boxed_1319_; uint8_t v_skipConstInApp_boxed_1320_; uint8_t v_skipInstances_boxed_1321_; lean_object* v_res_1322_; 
v_usedLetOnly_boxed_1319_ = lean_unbox(v_usedLetOnly_1307_);
v_skipConstInApp_boxed_1320_ = lean_unbox(v_skipConstInApp_1308_);
v_skipInstances_boxed_1321_ = lean_unbox(v_skipInstances_1309_);
v_res_1322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1304_, v_pre_1305_, v_post_1306_, v_usedLetOnly_boxed_1319_, v_skipConstInApp_boxed_1320_, v_skipInstances_boxed_1321_, v_body_1310_, v_x_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1312_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1323_, lean_object* v_post_1324_, uint8_t v_usedLetOnly_1325_, uint8_t v_skipConstInApp_1326_, uint8_t v_skipInstances_1327_, lean_object* v_fvars_1328_, lean_object* v_e_1329_, lean_object* v_a_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
if (lean_obj_tag(v_e_1329_) == 8)
{
lean_object* v_declName_1337_; lean_object* v_type_1338_; lean_object* v_value_1339_; lean_object* v_body_1340_; uint8_t v_nondep_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_declName_1337_ = lean_ctor_get(v_e_1329_, 0);
lean_inc(v_declName_1337_);
v_type_1338_ = lean_ctor_get(v_e_1329_, 1);
lean_inc_ref(v_type_1338_);
v_value_1339_ = lean_ctor_get(v_e_1329_, 2);
lean_inc_ref(v_value_1339_);
v_body_1340_ = lean_ctor_get(v_e_1329_, 3);
lean_inc_ref(v_body_1340_);
v_nondep_1341_ = lean_ctor_get_uint8(v_e_1329_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1329_);
v___x_1342_ = lean_expr_instantiate_rev(v_type_1338_, v_fvars_1328_);
lean_dec_ref(v_type_1338_);
lean_inc_ref(v_post_1324_);
lean_inc_ref(v_pre_1323_);
v___x_1343_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1323_, v_post_1324_, v_usedLetOnly_1325_, v_skipConstInApp_1326_, v_skipInstances_1327_, v___x_1342_, v_a_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1343_);
v_fst_1345_ = lean_ctor_get(v_a_1344_, 0);
lean_inc(v_fst_1345_);
v_snd_1346_ = lean_ctor_get(v_a_1344_, 1);
lean_inc(v_snd_1346_);
lean_dec(v_a_1344_);
v___x_1347_ = lean_expr_instantiate_rev(v_value_1339_, v_fvars_1328_);
lean_dec_ref(v_value_1339_);
lean_inc_ref(v_post_1324_);
lean_inc_ref(v_pre_1323_);
v___x_1348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1323_, v_post_1324_, v_usedLetOnly_1325_, v_skipConstInApp_1326_, v_skipInstances_1327_, v___x_1347_, v_a_1330_, v_snd_1346_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v_fst_1350_; lean_object* v_snd_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___f_1355_; uint8_t v___x_1356_; lean_object* v___x_1357_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref(v___x_1348_);
v_fst_1350_ = lean_ctor_get(v_a_1349_, 0);
lean_inc(v_fst_1350_);
v_snd_1351_ = lean_ctor_get(v_a_1349_, 1);
lean_inc(v_snd_1351_);
lean_dec(v_a_1349_);
v___x_1352_ = lean_box(v_usedLetOnly_1325_);
v___x_1353_ = lean_box(v_skipConstInApp_1326_);
v___x_1354_ = lean_box(v_skipInstances_1327_);
v___f_1355_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1355_, 0, v_fvars_1328_);
lean_closure_set(v___f_1355_, 1, v_pre_1323_);
lean_closure_set(v___f_1355_, 2, v_post_1324_);
lean_closure_set(v___f_1355_, 3, v___x_1352_);
lean_closure_set(v___f_1355_, 4, v___x_1353_);
lean_closure_set(v___f_1355_, 5, v___x_1354_);
lean_closure_set(v___f_1355_, 6, v_body_1340_);
v___x_1356_ = 0;
v___x_1357_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1337_, v_fst_1345_, v_fst_1350_, v___f_1355_, v_nondep_1341_, v___x_1356_, v_a_1330_, v_snd_1351_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
return v___x_1357_;
}
else
{
lean_dec(v_fst_1345_);
lean_dec_ref(v_body_1340_);
lean_dec(v_declName_1337_);
lean_dec_ref(v_fvars_1328_);
lean_dec_ref(v_post_1324_);
lean_dec_ref(v_pre_1323_);
return v___x_1348_;
}
}
else
{
lean_dec_ref(v_body_1340_);
lean_dec_ref(v_value_1339_);
lean_dec(v_declName_1337_);
lean_dec_ref(v_fvars_1328_);
lean_dec_ref(v_post_1324_);
lean_dec_ref(v_pre_1323_);
return v___x_1343_;
}
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_expr_instantiate_rev(v_e_1329_, v_fvars_1328_);
lean_dec_ref(v_e_1329_);
lean_inc_ref(v_post_1324_);
lean_inc_ref(v_pre_1323_);
v___x_1359_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1323_, v_post_1324_, v_usedLetOnly_1325_, v_skipConstInApp_1326_, v_skipInstances_1327_, v___x_1358_, v_a_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v_fst_1361_; lean_object* v_snd_1362_; uint8_t v___x_1363_; uint8_t v___x_1364_; lean_object* v___x_1365_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
v_fst_1361_ = lean_ctor_get(v_a_1360_, 0);
lean_inc(v_fst_1361_);
v_snd_1362_ = lean_ctor_get(v_a_1360_, 1);
lean_inc(v_snd_1362_);
lean_dec(v_a_1360_);
v___x_1363_ = 0;
v___x_1364_ = 1;
v___x_1365_ = l_Lean_Meta_mkLetFVars(v_fvars_1328_, v_fst_1361_, v_usedLetOnly_1325_, v___x_1363_, v___x_1364_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec_ref(v_fvars_1328_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref(v___x_1365_);
v___x_1367_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1323_, v_post_1324_, v_usedLetOnly_1325_, v_skipConstInApp_1326_, v_skipInstances_1327_, v_a_1366_, v_a_1330_, v_snd_1362_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
return v___x_1367_;
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_snd_1362_);
lean_dec_ref(v_post_1324_);
lean_dec_ref(v_pre_1323_);
v_a_1368_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1365_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1365_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1328_);
lean_dec_ref(v_post_1324_);
lean_dec_ref(v_pre_1323_);
return v___x_1359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_pre_1376_, lean_object* v_post_1377_, uint8_t v_usedLetOnly_1378_, uint8_t v_skipConstInApp_1379_, uint8_t v_skipInstances_1380_, size_t v_sz_1381_, size_t v_i_1382_, lean_object* v_bs_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
uint8_t v___x_1391_; 
v___x_1391_ = lean_usize_dec_lt(v_i_1382_, v_sz_1381_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1376_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_bs_1383_);
lean_ctor_set(v___x_1392_, 1, v___y_1385_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
else
{
lean_object* v_v_1394_; lean_object* v___x_1395_; 
v_v_1394_ = lean_array_uget_borrowed(v_bs_1383_, v_i_1382_);
lean_inc(v_v_1394_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1376_);
v___x_1395_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1376_, v_post_1377_, v_usedLetOnly_1378_, v_skipConstInApp_1379_, v_skipInstances_1380_, v_v_1394_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v_fst_1397_; lean_object* v_snd_1398_; lean_object* v___x_1399_; lean_object* v_bs_x27_1400_; size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref(v___x_1395_);
v_fst_1397_ = lean_ctor_get(v_a_1396_, 0);
lean_inc(v_fst_1397_);
v_snd_1398_ = lean_ctor_get(v_a_1396_, 1);
lean_inc(v_snd_1398_);
lean_dec(v_a_1396_);
v___x_1399_ = lean_unsigned_to_nat(0u);
v_bs_x27_1400_ = lean_array_uset(v_bs_1383_, v_i_1382_, v___x_1399_);
v___x_1401_ = ((size_t)1ULL);
v___x_1402_ = lean_usize_add(v_i_1382_, v___x_1401_);
v___x_1403_ = lean_array_uset(v_bs_x27_1400_, v_i_1382_, v_fst_1397_);
v_i_1382_ = v___x_1402_;
v_bs_1383_ = v___x_1403_;
v___y_1385_ = v_snd_1398_;
goto _start;
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v_bs_1383_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1376_);
v_a_1405_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1395_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1395_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object* v_pre_1413_, lean_object* v_post_1414_, uint8_t v_usedLetOnly_1415_, uint8_t v_skipConstInApp_1416_, uint8_t v_skipInstances_1417_, lean_object* v___x_1418_, lean_object* v___y_1419_, lean_object* v_b_1420_, lean_object* v_a_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1413_, v_post_1414_, v_usedLetOnly_1415_, v_skipConstInApp_1416_, v_skipInstances_1417_, v___x_1418_, v___y_1419_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1447_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1447_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1447_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_fst_1433_; lean_object* v_snd_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1446_; 
v_fst_1433_ = lean_ctor_get(v_a_1429_, 0);
v_snd_1434_ = lean_ctor_get(v_a_1429_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_a_1429_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1436_ = v_a_1429_;
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_snd_1434_);
lean_inc(v_fst_1433_);
lean_dec(v_a_1429_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1438_ = lean_array_fset(v_b_1420_, v_a_1421_, v_fst_1433_);
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1439_);
v___x_1441_ = v___x_1436_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_snd_1434_);
v___x_1441_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1441_);
v___x_1443_ = v___x_1431_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec_ref(v_b_1420_);
v_a_1448_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1428_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1428_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v_pre_1456_, lean_object* v_post_1457_, lean_object* v_usedLetOnly_1458_, lean_object* v_skipConstInApp_1459_, lean_object* v_skipInstances_1460_, lean_object* v___x_1461_, lean_object* v___y_1462_, lean_object* v_b_1463_, lean_object* v_a_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v_usedLetOnly_boxed_1471_; uint8_t v_skipConstInApp_boxed_1472_; uint8_t v_skipInstances_boxed_1473_; lean_object* v_res_1474_; 
v_usedLetOnly_boxed_1471_ = lean_unbox(v_usedLetOnly_1458_);
v_skipConstInApp_boxed_1472_ = lean_unbox(v_skipConstInApp_1459_);
v_skipInstances_boxed_1473_ = lean_unbox(v_skipInstances_1460_);
v_res_1474_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1456_, v_post_1457_, v_usedLetOnly_boxed_1471_, v_skipConstInApp_boxed_1472_, v_skipInstances_boxed_1473_, v___x_1461_, v___y_1462_, v_b_1463_, v_a_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v_a_1464_);
lean_dec(v___y_1462_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object* v_upperBound_1475_, lean_object* v___x_1476_, lean_object* v_pre_1477_, lean_object* v_post_1478_, uint8_t v_usedLetOnly_1479_, uint8_t v_skipConstInApp_1480_, uint8_t v_skipInstances_1481_, lean_object* v_a_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___y_1492_; uint8_t v___x_1526_; 
v___x_1526_ = lean_nat_dec_lt(v_a_1482_, v_upperBound_1475_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec(v_a_1482_);
lean_dec_ref(v_post_1478_);
lean_dec_ref(v_pre_1477_);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v_b_1483_);
lean_ctor_set(v___x_1527_, 1, v___y_1485_);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = lean_array_fget_borrowed(v_b_1483_, v_a_1482_);
v___x_1530_ = lean_array_get_size(v___x_1476_);
v___x_1531_ = lean_nat_dec_lt(v_a_1482_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___f_1535_; 
lean_inc(v___x_1529_);
v___x_1532_ = lean_box(v_usedLetOnly_1479_);
v___x_1533_ = lean_box(v_skipConstInApp_1480_);
v___x_1534_ = lean_box(v_skipInstances_1481_);
lean_inc(v_a_1482_);
lean_inc(v___y_1484_);
lean_inc_ref(v_post_1478_);
lean_inc_ref(v_pre_1477_);
v___f_1535_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1535_, 0, v_pre_1477_);
lean_closure_set(v___f_1535_, 1, v_post_1478_);
lean_closure_set(v___f_1535_, 2, v___x_1532_);
lean_closure_set(v___f_1535_, 3, v___x_1533_);
lean_closure_set(v___f_1535_, 4, v___x_1534_);
lean_closure_set(v___f_1535_, 5, v___x_1529_);
lean_closure_set(v___f_1535_, 6, v___y_1484_);
lean_closure_set(v___f_1535_, 7, v_b_1483_);
lean_closure_set(v___f_1535_, 8, v_a_1482_);
v___y_1492_ = v___f_1535_;
goto v___jp_1491_;
}
else
{
lean_object* v___x_1536_; uint8_t v_isInstance_1537_; 
v___x_1536_ = lean_array_fget_borrowed(v___x_1476_, v_a_1482_);
v_isInstance_1537_ = lean_ctor_get_uint8(v___x_1536_, sizeof(void*)*1 + 4);
if (v_isInstance_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___f_1541_; 
lean_inc(v___x_1529_);
v___x_1538_ = lean_box(v_usedLetOnly_1479_);
v___x_1539_ = lean_box(v_skipConstInApp_1480_);
v___x_1540_ = lean_box(v_skipInstances_1481_);
lean_inc(v_a_1482_);
lean_inc(v___y_1484_);
lean_inc_ref(v_post_1478_);
lean_inc_ref(v_pre_1477_);
v___f_1541_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1541_, 0, v_pre_1477_);
lean_closure_set(v___f_1541_, 1, v_post_1478_);
lean_closure_set(v___f_1541_, 2, v___x_1538_);
lean_closure_set(v___f_1541_, 3, v___x_1539_);
lean_closure_set(v___f_1541_, 4, v___x_1540_);
lean_closure_set(v___f_1541_, 5, v___x_1529_);
lean_closure_set(v___f_1541_, 6, v___y_1484_);
lean_closure_set(v___f_1541_, 7, v_b_1483_);
lean_closure_set(v___f_1541_, 8, v_a_1482_);
v___y_1492_ = v___f_1541_;
goto v___jp_1491_;
}
else
{
lean_object* v___x_1542_; lean_object* v___f_1543_; 
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_b_1483_);
v___f_1543_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1543_, 0, v___x_1542_);
v___y_1492_ = v___f_1543_;
goto v___jp_1491_;
}
}
}
v___jp_1491_:
{
lean_object* v___x_1493_; 
lean_inc(v___y_1489_);
lean_inc_ref(v___y_1488_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
v___x_1493_ = lean_apply_6(v___y_1492_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, lean_box(0));
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1517_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1517_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1517_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_fst_1498_; 
v_fst_1498_ = lean_ctor_get(v_a_1494_, 0);
lean_inc(v_fst_1498_);
if (lean_obj_tag(v_fst_1498_) == 0)
{
lean_object* v_snd_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_a_1482_);
lean_dec_ref(v_post_1478_);
lean_dec_ref(v_pre_1477_);
v_snd_1499_ = lean_ctor_get(v_a_1494_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_a_1494_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_a_1494_, 0);
lean_dec(v_unused_1511_);
v___x_1501_ = v_a_1494_;
v_isShared_1502_ = v_isSharedCheck_1510_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_snd_1499_);
lean_dec(v_a_1494_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1510_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_a_1503_; lean_object* v___x_1505_; 
v_a_1503_ = lean_ctor_get(v_fst_1498_, 0);
lean_inc(v_a_1503_);
lean_dec_ref(v_fst_1498_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v_a_1503_);
v___x_1505_ = v___x_1501_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_snd_1499_);
v___x_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1507_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1505_);
v___x_1507_ = v___x_1496_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
else
{
lean_object* v_snd_1512_; lean_object* v_a_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_del_object(v___x_1496_);
v_snd_1512_ = lean_ctor_get(v_a_1494_, 1);
lean_inc(v_snd_1512_);
lean_dec(v_a_1494_);
v_a_1513_ = lean_ctor_get(v_fst_1498_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v_fst_1498_);
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = lean_nat_add(v_a_1482_, v___x_1514_);
lean_dec(v_a_1482_);
v_a_1482_ = v___x_1515_;
v_b_1483_ = v_a_1513_;
v___y_1485_ = v_snd_1512_;
goto _start;
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec(v_a_1482_);
lean_dec_ref(v_post_1478_);
lean_dec_ref(v_pre_1477_);
v_a_1518_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1493_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1493_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1544_, lean_object* v_pre_1545_, lean_object* v_post_1546_, uint8_t v_usedLetOnly_1547_, uint8_t v_skipConstInApp_1548_, lean_object* v_x_1549_, lean_object* v_x_1550_, lean_object* v_x_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_f_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; 
if (lean_obj_tag(v_x_1549_) == 5)
{
lean_object* v_fn_1615_; lean_object* v_arg_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_fn_1615_ = lean_ctor_get(v_x_1549_, 0);
lean_inc_ref(v_fn_1615_);
v_arg_1616_ = lean_ctor_get(v_x_1549_, 1);
lean_inc_ref(v_arg_1616_);
lean_dec_ref(v_x_1549_);
v___x_1617_ = lean_array_set(v_x_1550_, v_x_1551_, v_arg_1616_);
v___x_1618_ = lean_unsigned_to_nat(1u);
v___x_1619_ = lean_nat_sub(v_x_1551_, v___x_1618_);
lean_dec(v_x_1551_);
v_x_1549_ = v_fn_1615_;
v_x_1550_ = v___x_1617_;
v_x_1551_ = v___x_1619_;
goto _start;
}
else
{
lean_dec(v_x_1551_);
if (v_skipConstInApp_1548_ == 0)
{
goto v___jp_1610_;
}
else
{
uint8_t v___x_1621_; 
v___x_1621_ = l_Lean_Expr_isConst(v_x_1549_);
if (v___x_1621_ == 0)
{
goto v___jp_1610_;
}
else
{
v_f_1560_ = v_x_1549_;
v___y_1561_ = v___y_1552_;
v___y_1562_ = v___y_1553_;
v___y_1563_ = v___y_1554_;
v___y_1564_ = v___y_1555_;
v___y_1565_ = v___y_1556_;
v___y_1566_ = v___y_1557_;
goto v___jp_1559_;
}
}
}
v___jp_1559_:
{
if (v_skipInstances_1544_ == 0)
{
size_t v_sz_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v_sz_1567_ = lean_array_size(v_x_1550_);
v___x_1568_ = ((size_t)0ULL);
lean_inc_ref(v_post_1546_);
lean_inc_ref(v_pre_1545_);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1545_, v_post_1546_, v_usedLetOnly_1547_, v_skipConstInApp_1548_, v_skipInstances_1544_, v_sz_1567_, v___x_1568_, v_x_1550_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v_fst_1571_; lean_object* v_snd_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref(v___x_1569_);
v_fst_1571_ = lean_ctor_get(v_a_1570_, 0);
lean_inc(v_fst_1571_);
v_snd_1572_ = lean_ctor_get(v_a_1570_, 1);
lean_inc(v_snd_1572_);
lean_dec(v_a_1570_);
v___x_1573_ = l_Lean_mkAppN(v_f_1560_, v_fst_1571_);
lean_dec(v_fst_1571_);
v___x_1574_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1545_, v_post_1546_, v_usedLetOnly_1547_, v_skipConstInApp_1548_, v_skipInstances_1544_, v___x_1573_, v___y_1561_, v_snd_1572_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1574_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v_f_1560_);
lean_dec_ref(v_post_1546_);
lean_dec_ref(v_pre_1545_);
v_a_1575_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1569_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1569_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_array_get_size(v_x_1550_);
lean_inc_ref(v_f_1560_);
v___x_1584_ = l_Lean_Meta_getFunInfoNArgs(v_f_1560_, v___x_1583_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v_paramInfo_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
v_paramInfo_1586_ = lean_ctor_get(v_a_1585_, 0);
lean_inc_ref(v_paramInfo_1586_);
lean_dec(v_a_1585_);
v___x_1587_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1546_);
lean_inc_ref(v_pre_1545_);
v___x_1588_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_1583_, v_paramInfo_1586_, v_pre_1545_, v_post_1546_, v_usedLetOnly_1547_, v_skipConstInApp_1548_, v_skipInstances_1544_, v___x_1587_, v_x_1550_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec_ref(v_paramInfo_1586_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v_fst_1590_; lean_object* v_snd_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref(v___x_1588_);
v_fst_1590_ = lean_ctor_get(v_a_1589_, 0);
lean_inc(v_fst_1590_);
v_snd_1591_ = lean_ctor_get(v_a_1589_, 1);
lean_inc(v_snd_1591_);
lean_dec(v_a_1589_);
v___x_1592_ = l_Lean_mkAppN(v_f_1560_, v_fst_1590_);
lean_dec(v_fst_1590_);
v___x_1593_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1545_, v_post_1546_, v_usedLetOnly_1547_, v_skipConstInApp_1548_, v_skipInstances_1544_, v___x_1592_, v___y_1561_, v_snd_1591_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1593_;
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v_f_1560_);
lean_dec_ref(v_post_1546_);
lean_dec_ref(v_pre_1545_);
v_a_1594_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1588_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1588_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v___y_1562_);
lean_dec_ref(v_f_1560_);
lean_dec_ref(v_x_1550_);
lean_dec_ref(v_post_1546_);
lean_dec_ref(v_pre_1545_);
v_a_1602_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1584_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1584_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
v___jp_1610_:
{
lean_object* v___x_1611_; 
lean_inc_ref(v_post_1546_);
lean_inc_ref(v_pre_1545_);
v___x_1611_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1545_, v_post_1546_, v_usedLetOnly_1547_, v_skipConstInApp_1548_, v_skipInstances_1544_, v_x_1549_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v_fst_1613_; lean_object* v_snd_1614_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___x_1611_);
v_fst_1613_ = lean_ctor_get(v_a_1612_, 0);
lean_inc(v_fst_1613_);
v_snd_1614_ = lean_ctor_get(v_a_1612_, 1);
lean_inc(v_snd_1614_);
lean_dec(v_a_1612_);
v_f_1560_ = v_fst_1613_;
v___y_1561_ = v___y_1552_;
v___y_1562_ = v_snd_1614_;
v___y_1563_ = v___y_1554_;
v___y_1564_ = v___y_1555_;
v___y_1565_ = v___y_1556_;
v___y_1566_ = v___y_1557_;
goto v___jp_1559_;
}
else
{
lean_dec_ref(v_x_1550_);
lean_dec_ref(v_post_1546_);
lean_dec_ref(v_pre_1545_);
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1622_, lean_object* v_pre_1623_, lean_object* v_e_1624_, lean_object* v_post_1625_, uint8_t v_usedLetOnly_1626_, uint8_t v_skipConstInApp_1627_, uint8_t v_skipInstances_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Core_checkSystem(v___x_1622_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref(v___x_1636_);
lean_inc_ref(v_pre_1623_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc_ref(v_e_1624_);
v___x_1637_ = lean_apply_7(v_pre_1623_, v_e_1624_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, lean_box(0));
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1699_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1699_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1699_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_fst_1642_; lean_object* v_snd_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1698_; 
v_fst_1642_ = lean_ctor_get(v_a_1638_, 0);
v_snd_1643_ = lean_ctor_get(v_a_1638_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_a_1638_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1645_ = v_a_1638_;
v_isShared_1646_ = v_isSharedCheck_1698_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_snd_1643_);
lean_inc(v_fst_1642_);
lean_dec(v_a_1638_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1698_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___y_1648_; 
switch(lean_obj_tag(v_fst_1642_))
{
case 0:
{
lean_object* v_e_1687_; lean_object* v___x_1689_; 
lean_dec_ref(v_post_1625_);
lean_dec_ref(v_e_1624_);
lean_dec_ref(v_pre_1623_);
v_e_1687_ = lean_ctor_get(v_fst_1642_, 0);
lean_inc_ref(v_e_1687_);
lean_dec_ref(v_fst_1642_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v_e_1687_);
v___x_1689_ = v___x_1645_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_e_1687_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_snd_1643_);
v___x_1689_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1691_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1689_);
v___x_1691_ = v___x_1640_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
case 1:
{
lean_object* v_e_1694_; lean_object* v___x_1695_; 
lean_del_object(v___x_1645_);
lean_del_object(v___x_1640_);
lean_dec_ref(v_e_1624_);
v_e_1694_ = lean_ctor_get(v_fst_1642_, 0);
lean_inc_ref(v_e_1694_);
lean_dec_ref(v_fst_1642_);
v___x_1695_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v_e_1694_, v___y_1629_, v_snd_1643_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1695_;
}
default: 
{
lean_object* v_e_x3f_1696_; 
lean_del_object(v___x_1645_);
lean_del_object(v___x_1640_);
v_e_x3f_1696_ = lean_ctor_get(v_fst_1642_, 0);
lean_inc(v_e_x3f_1696_);
lean_dec_ref(v_fst_1642_);
if (lean_obj_tag(v_e_x3f_1696_) == 0)
{
v___y_1648_ = v_e_1624_;
goto v___jp_1647_;
}
else
{
lean_object* v_val_1697_; 
lean_dec_ref(v_e_1624_);
v_val_1697_ = lean_ctor_get(v_e_x3f_1696_, 0);
lean_inc(v_val_1697_);
lean_dec_ref(v_e_x3f_1696_);
v___y_1648_ = v_val_1697_;
goto v___jp_1647_;
}
}
}
v___jp_1647_:
{
switch(lean_obj_tag(v___y_1648_))
{
case 7:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1650_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v___x_1649_, v___y_1648_, v___y_1629_, v_snd_1643_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1650_;
}
case 6:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v___x_1651_, v___y_1648_, v___y_1629_, v_snd_1643_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1652_;
}
case 8:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v___x_1653_, v___y_1648_, v___y_1629_, v_snd_1643_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1654_;
}
case 5:
{
lean_object* v_dummy_1655_; lean_object* v_nargs_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_dummy_1655_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1656_ = l_Lean_Expr_getAppNumArgs(v___y_1648_);
lean_inc(v_nargs_1656_);
v___x_1657_ = lean_mk_array(v_nargs_1656_, v_dummy_1655_);
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_nat_sub(v_nargs_1656_, v___x_1658_);
lean_dec(v_nargs_1656_);
v___x_1660_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1628_, v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v___y_1648_, v___x_1657_, v___x_1659_, v___y_1629_, v_snd_1643_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1660_;
}
case 10:
{
lean_object* v_data_1661_; lean_object* v_expr_1662_; lean_object* v___x_1663_; 
v_data_1661_ = lean_ctor_get(v___y_1648_, 0);
v_expr_1662_ = lean_ctor_get(v___y_1648_, 1);
lean_inc_ref(v_expr_1662_);
lean_inc_ref(v_post_1625_);
lean_inc_ref(v_pre_1623_);
v___x_1663_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v_expr_1662_, v___y_1629_, v_snd_1643_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v_fst_1665_; lean_object* v_snd_1666_; size_t v___x_1667_; size_t v___x_1668_; uint8_t v___x_1669_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref(v___x_1663_);
v_fst_1665_ = lean_ctor_get(v_a_1664_, 0);
lean_inc(v_fst_1665_);
v_snd_1666_ = lean_ctor_get(v_a_1664_, 1);
lean_inc(v_snd_1666_);
lean_dec(v_a_1664_);
v___x_1667_ = lean_ptr_addr(v_expr_1662_);
v___x_1668_ = lean_ptr_addr(v_fst_1665_);
v___x_1669_ = lean_usize_dec_eq(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_inc(v_data_1661_);
lean_dec_ref(v___y_1648_);
v___x_1670_ = l_Lean_Expr_mdata___override(v_data_1661_, v_fst_1665_);
v___x_1671_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v___x_1670_, v___y_1629_, v_snd_1666_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1671_;
}
else
{
lean_object* v___x_1672_; 
lean_dec(v_fst_1665_);
v___x_1672_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v___y_1648_, v___y_1629_, v_snd_1666_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1672_;
}
}
else
{
lean_dec_ref(v___y_1648_);
lean_dec_ref(v_post_1625_);
lean_dec_ref(v_pre_1623_);
return v___x_1663_;
}
}
case 11:
{
lean_object* v_typeName_1673_; lean_object* v_idx_1674_; lean_object* v_struct_1675_; lean_object* v___x_1676_; 
v_typeName_1673_ = lean_ctor_get(v___y_1648_, 0);
v_idx_1674_ = lean_ctor_get(v___y_1648_, 1);
v_struct_1675_ = lean_ctor_get(v___y_1648_, 2);
lean_inc_ref(v_struct_1675_);
lean_inc_ref(v_post_1625_);
lean_inc_ref(v_pre_1623_);
v___x_1676_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v_struct_1675_, v___y_1629_, v_snd_1643_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v_fst_1678_; lean_object* v_snd_1679_; size_t v___x_1680_; size_t v___x_1681_; uint8_t v___x_1682_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref(v___x_1676_);
v_fst_1678_ = lean_ctor_get(v_a_1677_, 0);
lean_inc(v_fst_1678_);
v_snd_1679_ = lean_ctor_get(v_a_1677_, 1);
lean_inc(v_snd_1679_);
lean_dec(v_a_1677_);
v___x_1680_ = lean_ptr_addr(v_struct_1675_);
v___x_1681_ = lean_ptr_addr(v_fst_1678_);
v___x_1682_ = lean_usize_dec_eq(v___x_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_inc(v_idx_1674_);
lean_inc(v_typeName_1673_);
lean_dec_ref(v___y_1648_);
v___x_1683_ = l_Lean_Expr_proj___override(v_typeName_1673_, v_idx_1674_, v_fst_1678_);
v___x_1684_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v___x_1683_, v___y_1629_, v_snd_1679_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; 
lean_dec(v_fst_1678_);
v___x_1685_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v___y_1648_, v___y_1629_, v_snd_1679_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1685_;
}
}
else
{
lean_dec_ref(v___y_1648_);
lean_dec_ref(v_post_1625_);
lean_dec_ref(v_pre_1623_);
return v___x_1676_;
}
}
default: 
{
lean_object* v___x_1686_; 
v___x_1686_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1623_, v_post_1625_, v_usedLetOnly_1626_, v_skipConstInApp_1627_, v_skipInstances_1628_, v___y_1648_, v___y_1629_, v_snd_1643_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1686_;
}
}
}
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec_ref(v_post_1625_);
lean_dec_ref(v_e_1624_);
lean_dec_ref(v_pre_1623_);
v_a_1700_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1637_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1637_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v___y_1630_);
lean_dec_ref(v_post_1625_);
lean_dec_ref(v_e_1624_);
lean_dec_ref(v_pre_1623_);
v_a_1708_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1636_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1636_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1716_, lean_object* v_pre_1717_, lean_object* v_e_1718_, lean_object* v_post_1719_, lean_object* v_usedLetOnly_1720_, lean_object* v_skipConstInApp_1721_, lean_object* v_skipInstances_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v_usedLetOnly_boxed_1730_; uint8_t v_skipConstInApp_boxed_1731_; uint8_t v_skipInstances_boxed_1732_; lean_object* v_res_1733_; 
v_usedLetOnly_boxed_1730_ = lean_unbox(v_usedLetOnly_1720_);
v_skipConstInApp_boxed_1731_ = lean_unbox(v_skipConstInApp_1721_);
v_skipInstances_boxed_1732_ = lean_unbox(v_skipInstances_1722_);
v_res_1733_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1716_, v_pre_1717_, v_e_1718_, v_post_1719_, v_usedLetOnly_boxed_1730_, v_skipConstInApp_boxed_1731_, v_skipInstances_boxed_1732_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1723_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1734_, lean_object* v_post_1735_, uint8_t v_usedLetOnly_1736_, uint8_t v_skipConstInApp_1737_, uint8_t v_skipInstances_1738_, lean_object* v_e_1739_, lean_object* v_a_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_inc(v_a_1740_);
v___x_1747_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1747_, 0, lean_box(0));
lean_closure_set(v___x_1747_, 1, lean_box(0));
lean_closure_set(v___x_1747_, 2, v_a_1740_);
v___x_1748_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1747_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1803_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1803_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1803_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1802_; 
v_fst_1753_ = lean_ctor_get(v_a_1749_, 0);
v_snd_1754_ = lean_ctor_get(v_a_1749_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_a_1749_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1756_ = v_a_1749_;
v_isShared_1757_ = v_isSharedCheck_1802_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snd_1754_);
lean_inc(v_fst_1753_);
lean_dec(v_a_1749_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1802_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1753_, v_e_1739_);
lean_dec(v_fst_1753_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; 
lean_del_object(v___x_1756_);
lean_del_object(v___x_1751_);
v___x_1759_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1760_ = lean_box(v_usedLetOnly_1736_);
v___x_1761_ = lean_box(v_skipConstInApp_1737_);
v___x_1762_ = lean_box(v_skipInstances_1738_);
lean_inc_ref(v_e_1739_);
v___f_1763_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1763_, 0, v___x_1759_);
lean_closure_set(v___f_1763_, 1, v_pre_1734_);
lean_closure_set(v___f_1763_, 2, v_e_1739_);
lean_closure_set(v___f_1763_, 3, v_post_1735_);
lean_closure_set(v___f_1763_, 4, v___x_1760_);
lean_closure_set(v___f_1763_, 5, v___x_1761_);
lean_closure_set(v___f_1763_, 6, v___x_1762_);
v___x_1764_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1763_, v_a_1740_, v_snd_1754_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v_fst_1766_; lean_object* v_snd_1767_; lean_object* v___f_1768_; lean_object* v___x_1769_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref(v___x_1764_);
v_fst_1766_ = lean_ctor_get(v_a_1765_, 0);
lean_inc_n(v_fst_1766_, 2);
v_snd_1767_ = lean_ctor_get(v_a_1765_, 1);
lean_inc(v_snd_1767_);
lean_dec(v_a_1765_);
lean_inc(v_a_1740_);
v___f_1768_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1768_, 0, v_a_1740_);
lean_closure_set(v___f_1768_, 1, v_e_1739_);
lean_closure_set(v___f_1768_, 2, v_fst_1766_);
v___x_1769_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1768_, v_snd_1767_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1786_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1786_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1786_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_snd_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1784_; 
v_snd_1774_ = lean_ctor_get(v_a_1770_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_a_1770_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v_a_1770_, 0);
lean_dec(v_unused_1785_);
v___x_1776_ = v_a_1770_;
v_isShared_1777_ = v_isSharedCheck_1784_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_snd_1774_);
lean_dec(v_a_1770_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1784_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v_fst_1766_);
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_fst_1766_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_snd_1774_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1779_);
v___x_1781_ = v___x_1772_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_fst_1766_);
v_a_1787_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1769_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1769_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_dec_ref(v_e_1739_);
return v___x_1764_;
}
}
else
{
lean_object* v_val_1795_; lean_object* v___x_1797_; 
lean_dec_ref(v_e_1739_);
lean_dec_ref(v_post_1735_);
lean_dec_ref(v_pre_1734_);
v_val_1795_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_val_1795_);
lean_dec_ref(v___x_1758_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v_val_1795_);
v___x_1797_ = v___x_1756_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_val_1795_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_snd_1754_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1797_);
v___x_1799_ = v___x_1751_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec_ref(v_e_1739_);
lean_dec_ref(v_post_1735_);
lean_dec_ref(v_pre_1734_);
v_a_1804_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1748_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1748_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1812_, lean_object* v_pre_1813_, lean_object* v_post_1814_, lean_object* v_usedLetOnly_1815_, lean_object* v_skipConstInApp_1816_, lean_object* v_skipInstances_1817_, lean_object* v_body_1818_, lean_object* v_x_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
uint8_t v_usedLetOnly_boxed_1827_; uint8_t v_skipConstInApp_boxed_1828_; uint8_t v_skipInstances_boxed_1829_; lean_object* v_res_1830_; 
v_usedLetOnly_boxed_1827_ = lean_unbox(v_usedLetOnly_1815_);
v_skipConstInApp_boxed_1828_ = lean_unbox(v_skipConstInApp_1816_);
v_skipInstances_boxed_1829_ = lean_unbox(v_skipInstances_1817_);
v_res_1830_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1812_, v_pre_1813_, v_post_1814_, v_usedLetOnly_boxed_1827_, v_skipConstInApp_boxed_1828_, v_skipInstances_boxed_1829_, v_body_1818_, v_x_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1820_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1831_, lean_object* v_post_1832_, uint8_t v_usedLetOnly_1833_, uint8_t v_skipConstInApp_1834_, uint8_t v_skipInstances_1835_, lean_object* v_fvars_1836_, lean_object* v_e_1837_, lean_object* v_a_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
if (lean_obj_tag(v_e_1837_) == 7)
{
lean_object* v_binderName_1845_; lean_object* v_binderType_1846_; lean_object* v_body_1847_; uint8_t v_binderInfo_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_binderName_1845_ = lean_ctor_get(v_e_1837_, 0);
lean_inc(v_binderName_1845_);
v_binderType_1846_ = lean_ctor_get(v_e_1837_, 1);
lean_inc_ref(v_binderType_1846_);
v_body_1847_ = lean_ctor_get(v_e_1837_, 2);
lean_inc_ref(v_body_1847_);
v_binderInfo_1848_ = lean_ctor_get_uint8(v_e_1837_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1837_);
v___x_1849_ = lean_expr_instantiate_rev(v_binderType_1846_, v_fvars_1836_);
lean_dec_ref(v_binderType_1846_);
lean_inc_ref(v_post_1832_);
lean_inc_ref(v_pre_1831_);
v___x_1850_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1831_, v_post_1832_, v_usedLetOnly_1833_, v_skipConstInApp_1834_, v_skipInstances_1835_, v___x_1849_, v_a_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v_fst_1852_; lean_object* v_snd_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___f_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref(v___x_1850_);
v_fst_1852_ = lean_ctor_get(v_a_1851_, 0);
lean_inc(v_fst_1852_);
v_snd_1853_ = lean_ctor_get(v_a_1851_, 1);
lean_inc(v_snd_1853_);
lean_dec(v_a_1851_);
v___x_1854_ = lean_box(v_usedLetOnly_1833_);
v___x_1855_ = lean_box(v_skipConstInApp_1834_);
v___x_1856_ = lean_box(v_skipInstances_1835_);
v___f_1857_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1857_, 0, v_fvars_1836_);
lean_closure_set(v___f_1857_, 1, v_pre_1831_);
lean_closure_set(v___f_1857_, 2, v_post_1832_);
lean_closure_set(v___f_1857_, 3, v___x_1854_);
lean_closure_set(v___f_1857_, 4, v___x_1855_);
lean_closure_set(v___f_1857_, 5, v___x_1856_);
lean_closure_set(v___f_1857_, 6, v_body_1847_);
v___x_1858_ = 0;
v___x_1859_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1845_, v_binderInfo_1848_, v_fst_1852_, v___f_1857_, v___x_1858_, v_a_1838_, v_snd_1853_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1859_;
}
else
{
lean_dec_ref(v_body_1847_);
lean_dec(v_binderName_1845_);
lean_dec_ref(v_fvars_1836_);
lean_dec_ref(v_post_1832_);
lean_dec_ref(v_pre_1831_);
return v___x_1850_;
}
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_expr_instantiate_rev(v_e_1837_, v_fvars_1836_);
lean_dec_ref(v_e_1837_);
lean_inc_ref(v_post_1832_);
lean_inc_ref(v_pre_1831_);
v___x_1861_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1831_, v_post_1832_, v_usedLetOnly_1833_, v_skipConstInApp_1834_, v_skipInstances_1835_, v___x_1860_, v_a_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v_fst_1863_; lean_object* v_snd_1864_; uint8_t v___x_1865_; uint8_t v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref(v___x_1861_);
v_fst_1863_ = lean_ctor_get(v_a_1862_, 0);
lean_inc(v_fst_1863_);
v_snd_1864_ = lean_ctor_get(v_a_1862_, 1);
lean_inc(v_snd_1864_);
lean_dec(v_a_1862_);
v___x_1865_ = 0;
v___x_1866_ = 1;
v___x_1867_ = 1;
v___x_1868_ = l_Lean_Meta_mkForallFVars(v_fvars_1836_, v_fst_1863_, v___x_1865_, v_usedLetOnly_1833_, v___x_1866_, v___x_1867_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec_ref(v_fvars_1836_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1868_);
v___x_1870_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1831_, v_post_1832_, v_usedLetOnly_1833_, v_skipConstInApp_1834_, v_skipInstances_1835_, v_a_1869_, v_a_1838_, v_snd_1864_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1870_;
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_snd_1864_);
lean_dec_ref(v_post_1832_);
lean_dec_ref(v_pre_1831_);
v_a_1871_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1868_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1868_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1836_);
lean_dec_ref(v_post_1832_);
lean_dec_ref(v_pre_1831_);
return v___x_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1879_, lean_object* v_pre_1880_, lean_object* v_post_1881_, uint8_t v_usedLetOnly_1882_, uint8_t v_skipConstInApp_1883_, uint8_t v_skipInstances_1884_, lean_object* v_body_1885_, lean_object* v_x_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_array_push(v_fvars_1879_, v_x_1886_);
v___x_1895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1880_, v_post_1881_, v_usedLetOnly_1882_, v_skipConstInApp_1883_, v_skipInstances_1884_, v___x_1894_, v_body_1885_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_1896_, lean_object* v_post_1897_, lean_object* v_usedLetOnly_1898_, lean_object* v_skipConstInApp_1899_, lean_object* v_skipInstances_1900_, lean_object* v_sz_1901_, lean_object* v_i_1902_, lean_object* v_bs_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
uint8_t v_usedLetOnly_boxed_1911_; uint8_t v_skipConstInApp_boxed_1912_; uint8_t v_skipInstances_boxed_1913_; size_t v_sz_boxed_1914_; size_t v_i_boxed_1915_; lean_object* v_res_1916_; 
v_usedLetOnly_boxed_1911_ = lean_unbox(v_usedLetOnly_1898_);
v_skipConstInApp_boxed_1912_ = lean_unbox(v_skipConstInApp_1899_);
v_skipInstances_boxed_1913_ = lean_unbox(v_skipInstances_1900_);
v_sz_boxed_1914_ = lean_unbox_usize(v_sz_1901_);
lean_dec(v_sz_1901_);
v_i_boxed_1915_ = lean_unbox_usize(v_i_1902_);
lean_dec(v_i_1902_);
v_res_1916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1896_, v_post_1897_, v_usedLetOnly_boxed_1911_, v_skipConstInApp_boxed_1912_, v_skipInstances_boxed_1913_, v_sz_boxed_1914_, v_i_boxed_1915_, v_bs_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1904_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1917_, lean_object* v_post_1918_, lean_object* v_usedLetOnly_1919_, lean_object* v_skipConstInApp_1920_, lean_object* v_skipInstances_1921_, lean_object* v_e_1922_, lean_object* v_a_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
uint8_t v_usedLetOnly_boxed_1930_; uint8_t v_skipConstInApp_boxed_1931_; uint8_t v_skipInstances_boxed_1932_; lean_object* v_res_1933_; 
v_usedLetOnly_boxed_1930_ = lean_unbox(v_usedLetOnly_1919_);
v_skipConstInApp_boxed_1931_ = lean_unbox(v_skipConstInApp_1920_);
v_skipInstances_boxed_1932_ = lean_unbox(v_skipInstances_1921_);
v_res_1933_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1917_, v_post_1918_, v_usedLetOnly_boxed_1930_, v_skipConstInApp_boxed_1931_, v_skipInstances_boxed_1932_, v_e_1922_, v_a_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v_a_1923_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1934_, lean_object* v_post_1935_, lean_object* v_usedLetOnly_1936_, lean_object* v_skipConstInApp_1937_, lean_object* v_skipInstances_1938_, lean_object* v_fvars_1939_, lean_object* v_e_1940_, lean_object* v_a_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
uint8_t v_usedLetOnly_boxed_1948_; uint8_t v_skipConstInApp_boxed_1949_; uint8_t v_skipInstances_boxed_1950_; lean_object* v_res_1951_; 
v_usedLetOnly_boxed_1948_ = lean_unbox(v_usedLetOnly_1936_);
v_skipConstInApp_boxed_1949_ = lean_unbox(v_skipConstInApp_1937_);
v_skipInstances_boxed_1950_ = lean_unbox(v_skipInstances_1938_);
v_res_1951_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1934_, v_post_1935_, v_usedLetOnly_boxed_1948_, v_skipConstInApp_boxed_1949_, v_skipInstances_boxed_1950_, v_fvars_1939_, v_e_1940_, v_a_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v_a_1941_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1952_, lean_object* v_post_1953_, lean_object* v_usedLetOnly_1954_, lean_object* v_skipConstInApp_1955_, lean_object* v_skipInstances_1956_, lean_object* v_fvars_1957_, lean_object* v_e_1958_, lean_object* v_a_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
uint8_t v_usedLetOnly_boxed_1966_; uint8_t v_skipConstInApp_boxed_1967_; uint8_t v_skipInstances_boxed_1968_; lean_object* v_res_1969_; 
v_usedLetOnly_boxed_1966_ = lean_unbox(v_usedLetOnly_1954_);
v_skipConstInApp_boxed_1967_ = lean_unbox(v_skipConstInApp_1955_);
v_skipInstances_boxed_1968_ = lean_unbox(v_skipInstances_1956_);
v_res_1969_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1952_, v_post_1953_, v_usedLetOnly_boxed_1966_, v_skipConstInApp_boxed_1967_, v_skipInstances_boxed_1968_, v_fvars_1957_, v_e_1958_, v_a_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v_a_1959_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1970_, lean_object* v_post_1971_, lean_object* v_usedLetOnly_1972_, lean_object* v_skipConstInApp_1973_, lean_object* v_skipInstances_1974_, lean_object* v_e_1975_, lean_object* v_a_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
uint8_t v_usedLetOnly_boxed_1983_; uint8_t v_skipConstInApp_boxed_1984_; uint8_t v_skipInstances_boxed_1985_; lean_object* v_res_1986_; 
v_usedLetOnly_boxed_1983_ = lean_unbox(v_usedLetOnly_1972_);
v_skipConstInApp_boxed_1984_ = lean_unbox(v_skipConstInApp_1973_);
v_skipInstances_boxed_1985_ = lean_unbox(v_skipInstances_1974_);
v_res_1986_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1970_, v_post_1971_, v_usedLetOnly_boxed_1983_, v_skipConstInApp_boxed_1984_, v_skipInstances_boxed_1985_, v_e_1975_, v_a_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v_a_1976_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1987_, lean_object* v_post_1988_, lean_object* v_usedLetOnly_1989_, lean_object* v_skipConstInApp_1990_, lean_object* v_skipInstances_1991_, lean_object* v_fvars_1992_, lean_object* v_e_1993_, lean_object* v_a_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
uint8_t v_usedLetOnly_boxed_2001_; uint8_t v_skipConstInApp_boxed_2002_; uint8_t v_skipInstances_boxed_2003_; lean_object* v_res_2004_; 
v_usedLetOnly_boxed_2001_ = lean_unbox(v_usedLetOnly_1989_);
v_skipConstInApp_boxed_2002_ = lean_unbox(v_skipConstInApp_1990_);
v_skipInstances_boxed_2003_ = lean_unbox(v_skipInstances_1991_);
v_res_2004_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1987_, v_post_1988_, v_usedLetOnly_boxed_2001_, v_skipConstInApp_boxed_2002_, v_skipInstances_boxed_2003_, v_fvars_1992_, v_e_1993_, v_a_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_a_1994_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_2005_, lean_object* v___x_2006_, lean_object* v_pre_2007_, lean_object* v_post_2008_, lean_object* v_usedLetOnly_2009_, lean_object* v_skipConstInApp_2010_, lean_object* v_skipInstances_2011_, lean_object* v_a_2012_, lean_object* v_b_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
uint8_t v_usedLetOnly_boxed_2021_; uint8_t v_skipConstInApp_boxed_2022_; uint8_t v_skipInstances_boxed_2023_; lean_object* v_res_2024_; 
v_usedLetOnly_boxed_2021_ = lean_unbox(v_usedLetOnly_2009_);
v_skipConstInApp_boxed_2022_ = lean_unbox(v_skipConstInApp_2010_);
v_skipInstances_boxed_2023_ = lean_unbox(v_skipInstances_2011_);
v_res_2024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2005_, v___x_2006_, v_pre_2007_, v_post_2008_, v_usedLetOnly_boxed_2021_, v_skipConstInApp_boxed_2022_, v_skipInstances_boxed_2023_, v_a_2012_, v_b_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2014_);
lean_dec_ref(v___x_2006_);
lean_dec(v_upperBound_2005_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2025_, lean_object* v_pre_2026_, lean_object* v_post_2027_, lean_object* v_usedLetOnly_2028_, lean_object* v_skipConstInApp_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
uint8_t v_skipInstances_boxed_2040_; uint8_t v_usedLetOnly_boxed_2041_; uint8_t v_skipConstInApp_boxed_2042_; lean_object* v_res_2043_; 
v_skipInstances_boxed_2040_ = lean_unbox(v_skipInstances_2025_);
v_usedLetOnly_boxed_2041_ = lean_unbox(v_usedLetOnly_2028_);
v_skipConstInApp_boxed_2042_ = lean_unbox(v_skipConstInApp_2029_);
v_res_2043_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2040_, v_pre_2026_, v_post_2027_, v_usedLetOnly_boxed_2041_, v_skipConstInApp_boxed_2042_, v_x_2030_, v_x_2031_, v_x_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2033_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2044_, lean_object* v_x_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_apply_1(v_x_2045_, lean_box(0));
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v___y_2046_);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2055_, lean_object* v_x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2055_, v_x_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2063_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_box(0);
v___x_2065_ = lean_unsigned_to_nat(16u);
v___x_2066_ = lean_mk_array(v___x_2065_, v___x_2064_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v___x_2067_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2071_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2071_, 0, lean_box(0));
lean_closure_set(v___x_2071_, 1, lean_box(0));
lean_closure_set(v___x_2071_, 2, v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2072_, lean_object* v_pre_2073_, lean_object* v_post_2074_, uint8_t v_usedLetOnly_2075_, uint8_t v_skipConstInApp_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_a_2085_; lean_object* v_fst_2086_; lean_object* v_snd_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; 
v___x_2083_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2084_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2083_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v_fst_2086_ = lean_ctor_get(v_a_2085_, 0);
lean_inc(v_fst_2086_);
v_snd_2087_ = lean_ctor_get(v_a_2085_, 1);
lean_inc(v_snd_2087_);
lean_dec(v_a_2085_);
v___x_2088_ = 0;
v___x_2089_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2073_, v_post_2074_, v_usedLetOnly_2075_, v_skipConstInApp_2076_, v___x_2088_, v_input_2072_, v_fst_2086_, v_snd_2087_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v_fst_2091_; lean_object* v_snd_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2111_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v___x_2089_);
v_fst_2091_ = lean_ctor_get(v_a_2090_, 0);
lean_inc(v_fst_2091_);
v_snd_2092_ = lean_ctor_get(v_a_2090_, 1);
lean_inc(v_snd_2092_);
lean_dec(v_a_2090_);
v___x_2093_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2093_, 0, lean_box(0));
lean_closure_set(v___x_2093_, 1, lean_box(0));
lean_closure_set(v___x_2093_, 2, v_fst_2086_);
v___x_2094_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2093_, v_snd_2092_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2111_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2111_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_snd_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2109_; 
v_snd_2099_ = lean_ctor_get(v_a_2095_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_a_2095_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; 
v_unused_2110_ = lean_ctor_get(v_a_2095_, 0);
lean_dec(v_unused_2110_);
v___x_2101_ = v_a_2095_;
v_isShared_2102_ = v_isSharedCheck_2109_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_snd_2099_);
lean_dec(v_a_2095_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2109_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v_fst_2091_);
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_fst_2091_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_snd_2099_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2104_);
v___x_2106_ = v___x_2097_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
else
{
lean_dec(v_fst_2086_);
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2112_, lean_object* v_pre_2113_, lean_object* v_post_2114_, lean_object* v_usedLetOnly_2115_, lean_object* v_skipConstInApp_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
uint8_t v_usedLetOnly_boxed_2123_; uint8_t v_skipConstInApp_boxed_2124_; lean_object* v_res_2125_; 
v_usedLetOnly_boxed_2123_ = lean_unbox(v_usedLetOnly_2115_);
v_skipConstInApp_boxed_2124_ = lean_unbox(v_skipConstInApp_2116_);
v_res_2125_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2112_, v_pre_2113_, v_post_2114_, v_usedLetOnly_boxed_2123_, v_skipConstInApp_boxed_2124_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2125_;
}
}
static uint64_t _init_l_Lean_Meta_expandCoe___closed__2(void){
_start:
{
uint8_t v___x_2128_; uint64_t v___x_2129_; 
v___x_2128_ = 3;
v___x_2129_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v___x_2136_; uint8_t v_foApprox_2137_; uint8_t v_ctxApprox_2138_; uint8_t v_quasiPatternApprox_2139_; uint8_t v_constApprox_2140_; uint8_t v_isDefEqStuckEx_2141_; uint8_t v_unificationHints_2142_; uint8_t v_proofIrrelevance_2143_; uint8_t v_assignSyntheticOpaque_2144_; uint8_t v_offsetCnstrs_2145_; uint8_t v_etaStruct_2146_; uint8_t v_univApprox_2147_; uint8_t v_iota_2148_; uint8_t v_beta_2149_; uint8_t v_proj_2150_; uint8_t v_zeta_2151_; uint8_t v_zetaDelta_2152_; uint8_t v_zetaUnused_2153_; uint8_t v_zetaHave_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2185_; 
v___x_2136_ = l_Lean_Meta_Context_config(v_a_2131_);
v_foApprox_2137_ = lean_ctor_get_uint8(v___x_2136_, 0);
v_ctxApprox_2138_ = lean_ctor_get_uint8(v___x_2136_, 1);
v_quasiPatternApprox_2139_ = lean_ctor_get_uint8(v___x_2136_, 2);
v_constApprox_2140_ = lean_ctor_get_uint8(v___x_2136_, 3);
v_isDefEqStuckEx_2141_ = lean_ctor_get_uint8(v___x_2136_, 4);
v_unificationHints_2142_ = lean_ctor_get_uint8(v___x_2136_, 5);
v_proofIrrelevance_2143_ = lean_ctor_get_uint8(v___x_2136_, 6);
v_assignSyntheticOpaque_2144_ = lean_ctor_get_uint8(v___x_2136_, 7);
v_offsetCnstrs_2145_ = lean_ctor_get_uint8(v___x_2136_, 8);
v_etaStruct_2146_ = lean_ctor_get_uint8(v___x_2136_, 10);
v_univApprox_2147_ = lean_ctor_get_uint8(v___x_2136_, 11);
v_iota_2148_ = lean_ctor_get_uint8(v___x_2136_, 12);
v_beta_2149_ = lean_ctor_get_uint8(v___x_2136_, 13);
v_proj_2150_ = lean_ctor_get_uint8(v___x_2136_, 14);
v_zeta_2151_ = lean_ctor_get_uint8(v___x_2136_, 15);
v_zetaDelta_2152_ = lean_ctor_get_uint8(v___x_2136_, 16);
v_zetaUnused_2153_ = lean_ctor_get_uint8(v___x_2136_, 17);
v_zetaHave_2154_ = lean_ctor_get_uint8(v___x_2136_, 18);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2156_ = v___x_2136_;
v_isShared_2157_ = v_isSharedCheck_2185_;
goto v_resetjp_2155_;
}
else
{
lean_dec(v___x_2136_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2185_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
uint8_t v_trackZetaDelta_2158_; lean_object* v_zetaDeltaSet_2159_; lean_object* v_lctx_2160_; lean_object* v_localInstances_2161_; lean_object* v_defEqCtx_x3f_2162_; lean_object* v_synthPendingDepth_2163_; lean_object* v_canUnfold_x3f_2164_; uint8_t v_univApprox_2165_; uint8_t v_inTypeClassResolution_2166_; uint8_t v_cacheInferType_2167_; uint8_t v___x_2168_; lean_object* v_config_2170_; 
v_trackZetaDelta_2158_ = lean_ctor_get_uint8(v_a_2131_, sizeof(void*)*7);
v_zetaDeltaSet_2159_ = lean_ctor_get(v_a_2131_, 1);
v_lctx_2160_ = lean_ctor_get(v_a_2131_, 2);
v_localInstances_2161_ = lean_ctor_get(v_a_2131_, 3);
v_defEqCtx_x3f_2162_ = lean_ctor_get(v_a_2131_, 4);
v_synthPendingDepth_2163_ = lean_ctor_get(v_a_2131_, 5);
v_canUnfold_x3f_2164_ = lean_ctor_get(v_a_2131_, 6);
v_univApprox_2165_ = lean_ctor_get_uint8(v_a_2131_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2166_ = lean_ctor_get_uint8(v_a_2131_, sizeof(void*)*7 + 2);
v_cacheInferType_2167_ = lean_ctor_get_uint8(v_a_2131_, sizeof(void*)*7 + 3);
v___x_2168_ = 3;
if (v_isShared_2157_ == 0)
{
v_config_2170_ = v___x_2156_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 0, v_foApprox_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 1, v_ctxApprox_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 2, v_quasiPatternApprox_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 3, v_constApprox_2140_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 4, v_isDefEqStuckEx_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 5, v_unificationHints_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 6, v_proofIrrelevance_2143_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 7, v_assignSyntheticOpaque_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 8, v_offsetCnstrs_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 10, v_etaStruct_2146_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 11, v_univApprox_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 12, v_iota_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 13, v_beta_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 14, v_proj_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 15, v_zeta_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 16, v_zetaDelta_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 17, v_zetaUnused_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, 18, v_zetaHave_2154_);
v_config_2170_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
uint64_t v___x_2171_; uint64_t v___x_2172_; uint64_t v___x_2173_; lean_object* v___f_2174_; lean_object* v___f_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; uint64_t v___x_2178_; uint64_t v___x_2179_; uint64_t v_key_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_ctor_set_uint8(v_config_2170_, 9, v___x_2168_);
v___x_2171_ = l_Lean_Meta_Context_configKey(v_a_2131_);
v___x_2172_ = 2ULL;
v___x_2173_ = lean_uint64_shift_right(v___x_2171_, v___x_2172_);
v___f_2174_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2175_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2176_ = 0;
v___x_2177_ = lean_box(0);
v___x_2178_ = lean_uint64_shift_left(v___x_2173_, v___x_2172_);
v___x_2179_ = lean_uint64_once(&l_Lean_Meta_expandCoe___closed__2, &l_Lean_Meta_expandCoe___closed__2_once, _init_l_Lean_Meta_expandCoe___closed__2);
v_key_2180_ = lean_uint64_lor(v___x_2178_, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2181_, 0, v_config_2170_);
lean_ctor_set_uint64(v___x_2181_, sizeof(void*)*1, v_key_2180_);
lean_inc(v_canUnfold_x3f_2164_);
lean_inc(v_synthPendingDepth_2163_);
lean_inc(v_defEqCtx_x3f_2162_);
lean_inc_ref(v_localInstances_2161_);
lean_inc_ref(v_lctx_2160_);
lean_inc(v_zetaDeltaSet_2159_);
v___x_2182_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v_zetaDeltaSet_2159_);
lean_ctor_set(v___x_2182_, 2, v_lctx_2160_);
lean_ctor_set(v___x_2182_, 3, v_localInstances_2161_);
lean_ctor_set(v___x_2182_, 4, v_defEqCtx_x3f_2162_);
lean_ctor_set(v___x_2182_, 5, v_synthPendingDepth_2163_);
lean_ctor_set(v___x_2182_, 6, v_canUnfold_x3f_2164_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*7, v_trackZetaDelta_2158_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*7 + 1, v_univApprox_2165_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2166_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*7 + 3, v_cacheInferType_2167_);
v___x_2183_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2130_, v___f_2175_, v___f_2174_, v___x_2176_, v___x_2176_, v___x_2177_, v___x_2182_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec_ref(v___x_2182_);
return v___x_2183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Meta_expandCoe(v_e_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2193_, lean_object* v_m_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2194_, v_a_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2197_, lean_object* v_m_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2197_, v_m_2198_, v_a_2199_);
lean_dec(v_a_2199_);
lean_dec_ref(v_m_2198_);
return v_res_2200_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
uint8_t v___x_2204_; 
v___x_2204_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2202_, v_x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2205_, lean_object* v_x_2206_, lean_object* v_x_2207_){
_start:
{
uint8_t v_res_2208_; lean_object* v_r_2209_; 
v_res_2208_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2205_, v_x_2206_, v_x_2207_);
lean_dec_ref(v_x_2207_);
lean_dec_ref(v_x_2206_);
v_r_2209_ = lean_box(v_res_2208_);
return v_r_2209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2210_, lean_object* v_a_2211_, lean_object* v_x_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2211_, v_x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2214_, lean_object* v_a_2215_, lean_object* v_x_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2214_, v_a_2215_, v_x_2216_);
lean_dec(v_x_2216_);
lean_dec(v_a_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2218_, lean_object* v___x_2219_, lean_object* v_pre_2220_, lean_object* v_post_2221_, uint8_t v_usedLetOnly_2222_, uint8_t v_skipConstInApp_2223_, uint8_t v_skipInstances_2224_, lean_object* v___x_2225_, lean_object* v_inst_2226_, lean_object* v_R_2227_, lean_object* v_a_2228_, lean_object* v_b_2229_, lean_object* v_c_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2218_, v___x_2219_, v_pre_2220_, v_post_2221_, v_usedLetOnly_2222_, v_skipConstInApp_2223_, v_skipInstances_2224_, v_a_2228_, v_b_2229_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2239_ = _args[0];
lean_object* v___x_2240_ = _args[1];
lean_object* v_pre_2241_ = _args[2];
lean_object* v_post_2242_ = _args[3];
lean_object* v_usedLetOnly_2243_ = _args[4];
lean_object* v_skipConstInApp_2244_ = _args[5];
lean_object* v_skipInstances_2245_ = _args[6];
lean_object* v___x_2246_ = _args[7];
lean_object* v_inst_2247_ = _args[8];
lean_object* v_R_2248_ = _args[9];
lean_object* v_a_2249_ = _args[10];
lean_object* v_b_2250_ = _args[11];
lean_object* v_c_2251_ = _args[12];
lean_object* v___y_2252_ = _args[13];
lean_object* v___y_2253_ = _args[14];
lean_object* v___y_2254_ = _args[15];
lean_object* v___y_2255_ = _args[16];
lean_object* v___y_2256_ = _args[17];
lean_object* v___y_2257_ = _args[18];
lean_object* v___y_2258_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2259_; uint8_t v_skipConstInApp_boxed_2260_; uint8_t v_skipInstances_boxed_2261_; lean_object* v_res_2262_; 
v_usedLetOnly_boxed_2259_ = lean_unbox(v_usedLetOnly_2243_);
v_skipConstInApp_boxed_2260_ = lean_unbox(v_skipConstInApp_2244_);
v_skipInstances_boxed_2261_ = lean_unbox(v_skipInstances_2245_);
v_res_2262_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2239_, v___x_2240_, v_pre_2241_, v_post_2242_, v_usedLetOnly_boxed_2259_, v_skipConstInApp_boxed_2260_, v_skipInstances_boxed_2261_, v___x_2246_, v_inst_2247_, v_R_2248_, v_a_2249_, v_b_2250_, v_c_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2252_);
lean_dec(v___x_2246_);
lean_dec_ref(v___x_2240_);
lean_dec(v_upperBound_2239_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2263_, lean_object* v_m_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2264_, v_a_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2267_, lean_object* v_m_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2267_, v_m_2268_, v_a_2269_);
lean_dec_ref(v_a_2269_);
lean_dec_ref(v_m_2268_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2271_, lean_object* v_name_2272_, uint8_t v_bi_2273_, lean_object* v_type_2274_, lean_object* v_k_2275_, uint8_t v_kind_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2272_, v_bi_2273_, v_type_2274_, v_k_2275_, v_kind_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_name_2286_, lean_object* v_bi_2287_, lean_object* v_type_2288_, lean_object* v_k_2289_, lean_object* v_kind_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
uint8_t v_bi_boxed_2298_; uint8_t v_kind_boxed_2299_; lean_object* v_res_2300_; 
v_bi_boxed_2298_ = lean_unbox(v_bi_2287_);
v_kind_boxed_2299_ = lean_unbox(v_kind_2290_);
v_res_2300_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2285_, v_name_2286_, v_bi_boxed_2298_, v_type_2288_, v_k_2289_, v_kind_boxed_2299_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2291_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2301_, lean_object* v_name_2302_, lean_object* v_type_2303_, lean_object* v_val_2304_, lean_object* v_k_2305_, uint8_t v_nondep_2306_, uint8_t v_kind_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2302_, v_type_2303_, v_val_2304_, v_k_2305_, v_nondep_2306_, v_kind_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2316_, lean_object* v_name_2317_, lean_object* v_type_2318_, lean_object* v_val_2319_, lean_object* v_k_2320_, lean_object* v_nondep_2321_, lean_object* v_kind_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
uint8_t v_nondep_boxed_2330_; uint8_t v_kind_boxed_2331_; lean_object* v_res_2332_; 
v_nondep_boxed_2330_ = lean_unbox(v_nondep_2321_);
v_kind_boxed_2331_ = lean_unbox(v_kind_2322_);
v_res_2332_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2316_, v_name_2317_, v_type_2318_, v_val_2319_, v_k_2320_, v_nondep_boxed_2330_, v_kind_boxed_2331_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2323_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2333_, lean_object* v_ref_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2334_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2341_, lean_object* v_ref_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2341_, v_ref_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2349_, lean_object* v_x_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2359_, lean_object* v_x_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2359_, v_x_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2361_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2369_, lean_object* v_m_2370_, lean_object* v_a_2371_, lean_object* v_b_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2370_, v_a_2371_, v_b_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2374_, lean_object* v_x_2375_, size_t v_x_2376_, lean_object* v_x_2377_){
_start:
{
uint8_t v___x_2378_; 
v___x_2378_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2375_, v_x_2376_, v_x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
size_t v_x_40434__boxed_2383_; uint8_t v_res_2384_; lean_object* v_r_2385_; 
v_x_40434__boxed_2383_ = lean_unbox_usize(v_x_2381_);
lean_dec(v_x_2381_);
v_res_2384_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2379_, v_x_2380_, v_x_40434__boxed_2383_, v_x_2382_);
lean_dec_ref(v_x_2382_);
lean_dec_ref(v_x_2380_);
v_r_2385_ = lean_box(v_res_2384_);
return v_r_2385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object* v_00_u03b2_2386_, lean_object* v_a_2387_, lean_object* v_x_2388_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_2387_, v_x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object* v_00_u03b2_2390_, lean_object* v_a_2391_, lean_object* v_x_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_2390_, v_a_2391_, v_x_2392_);
lean_dec(v_x_2392_);
lean_dec_ref(v_a_2391_);
return v_res_2393_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2394_, lean_object* v_a_2395_, lean_object* v_x_2396_){
_start:
{
uint8_t v___x_2397_; 
v___x_2397_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2395_, v_x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2398_, lean_object* v_a_2399_, lean_object* v_x_2400_){
_start:
{
uint8_t v_res_2401_; lean_object* v_r_2402_; 
v_res_2401_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2398_, v_a_2399_, v_x_2400_);
lean_dec(v_x_2400_);
lean_dec_ref(v_a_2399_);
v_r_2402_ = lean_box(v_res_2401_);
return v_r_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2403_, lean_object* v_data_2404_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2406_, lean_object* v_a_2407_, lean_object* v_b_2408_, lean_object* v_x_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2407_, v_b_2408_, v_x_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2411_, lean_object* v_keys_2412_, lean_object* v_vals_2413_, lean_object* v_heq_2414_, lean_object* v_i_2415_, lean_object* v_k_2416_){
_start:
{
uint8_t v___x_2417_; 
v___x_2417_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2412_, v_i_2415_, v_k_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2418_, lean_object* v_keys_2419_, lean_object* v_vals_2420_, lean_object* v_heq_2421_, lean_object* v_i_2422_, lean_object* v_k_2423_){
_start:
{
uint8_t v_res_2424_; lean_object* v_r_2425_; 
v_res_2424_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2418_, v_keys_2419_, v_vals_2420_, v_heq_2421_, v_i_2422_, v_k_2423_);
lean_dec_ref(v_k_2423_);
lean_dec_ref(v_vals_2420_);
lean_dec_ref(v_keys_2419_);
v_r_2425_ = lean_box(v_res_2424_);
return v_r_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2426_, lean_object* v_i_2427_, lean_object* v_source_2428_, lean_object* v_target_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2427_, v_source_2428_, v_target_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2431_, lean_object* v_x_2432_, lean_object* v_x_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2432_, v_x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2435_, lean_object* v_decl_2436_, lean_object* v_ref_2437_){
_start:
{
lean_object* v_defValue_2439_; lean_object* v_descr_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2467_; 
v_defValue_2439_ = lean_ctor_get(v_decl_2436_, 0);
v_descr_2440_ = lean_ctor_get(v_decl_2436_, 1);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_decl_2436_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2442_ = v_decl_2436_;
v_isShared_2443_ = v_isSharedCheck_2467_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_descr_2440_);
lean_inc(v_defValue_2439_);
lean_dec(v_decl_2436_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2467_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2444_ = lean_alloc_ctor(1, 0, 1);
v___x_2445_ = lean_unbox(v_defValue_2439_);
lean_ctor_set_uint8(v___x_2444_, 0, v___x_2445_);
lean_inc_n(v_name_2435_, 2);
v___x_2446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2446_, 0, v_name_2435_);
lean_ctor_set(v___x_2446_, 1, v_ref_2437_);
lean_ctor_set(v___x_2446_, 2, v___x_2444_);
lean_ctor_set(v___x_2446_, 3, v_descr_2440_);
v___x_2447_ = lean_register_option(v_name_2435_, v___x_2446_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2457_; 
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2457_ == 0)
{
lean_object* v_unused_2458_; 
v_unused_2458_ = lean_ctor_get(v___x_2447_, 0);
lean_dec(v_unused_2458_);
v___x_2449_ = v___x_2447_;
v_isShared_2450_ = v_isSharedCheck_2457_;
goto v_resetjp_2448_;
}
else
{
lean_dec(v___x_2447_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2457_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 1, v_defValue_2439_);
lean_ctor_set(v___x_2442_, 0, v_name_2435_);
v___x_2452_ = v___x_2442_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_name_2435_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_defValue_2439_);
v___x_2452_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2454_; 
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2452_);
v___x_2454_ = v___x_2449_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_del_object(v___x_2442_);
lean_dec(v_defValue_2439_);
lean_dec(v_name_2435_);
v_a_2459_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2447_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2447_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2468_, lean_object* v_decl_2469_, lean_object* v_ref_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2468_, v_decl_2469_, v_ref_2470_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2486_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2487_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2488_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2489_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2486_, v___x_2487_, v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_ref_2498_; lean_object* v___x_2499_; lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2508_; 
v_ref_2498_ = lean_ctor_get(v___y_2495_, 5);
v___x_2499_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2508_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2508_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
lean_inc(v_ref_2498_);
v___x_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2504_, 0, v_ref_2498_);
lean_ctor_set(v___x_2504_, 1, v_a_2500_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set_tag(v___x_2502_, 1);
lean_ctor_set(v___x_2502_, 0, v___x_2504_);
v___x_2506_ = v___x_2502_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
return v_res_2515_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2527_ = l_Lean_stringToMessageData(v___x_2526_);
return v___x_2527_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2530_ = l_Lean_stringToMessageData(v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2531_, lean_object* v_expectedType_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v___x_2538_; 
lean_inc(v_a_2536_);
lean_inc_ref(v_a_2535_);
lean_inc(v_a_2534_);
lean_inc_ref(v_a_2533_);
lean_inc_ref(v_expr_2531_);
v___x_2538_ = lean_infer_type(v_expr_2531_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2540_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc_n(v_a_2539_, 2);
lean_dec_ref(v___x_2538_);
v___x_2540_ = l_Lean_Meta_getLevel(v_a_2539_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2542_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref(v___x_2540_);
lean_inc_ref(v_expectedType_2532_);
v___x_2542_ = l_Lean_Meta_getLevel(v_expectedType_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___x_2542_);
v___x_2544_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2545_ = lean_box(0);
v___x_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2546_, 0, v_a_2543_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2547_, 0, v_a_2541_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
lean_inc_ref(v___x_2547_);
v___x_2548_ = l_Lean_mkConst(v___x_2544_, v___x_2547_);
v___x_2549_ = lean_unsigned_to_nat(3u);
v___x_2550_ = lean_mk_empty_array_with_capacity(v___x_2549_);
lean_inc(v_a_2539_);
v___x_2551_ = lean_array_push(v___x_2550_, v_a_2539_);
lean_inc_ref(v_expr_2531_);
v___x_2552_ = lean_array_push(v___x_2551_, v_expr_2531_);
lean_inc_ref(v_expectedType_2532_);
v___x_2553_ = lean_array_push(v___x_2552_, v_expectedType_2532_);
v___x_2554_ = l_Lean_mkAppN(v___x_2548_, v___x_2553_);
lean_dec_ref(v___x_2553_);
v___x_2555_ = lean_box(0);
v___x_2556_ = l_Lean_Meta_trySynthInstance(v___x_2554_, v___x_2555_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2654_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2654_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2654_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
switch(lean_obj_tag(v_a_2557_))
{
case 0:
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
lean_dec_ref(v___x_2547_);
lean_dec(v_a_2539_);
lean_dec_ref(v_expectedType_2532_);
lean_dec_ref(v_expr_2531_);
v___x_2561_ = lean_box(0);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2561_);
v___x_2563_ = v___x_2559_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
case 1:
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2649_; 
lean_del_object(v___x_2559_);
v_a_2565_ = lean_ctor_get(v_a_2557_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_a_2557_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2567_ = v_a_2557_;
v_isShared_2568_ = v_isSharedCheck_2649_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v_a_2557_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2649_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2569_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2570_ = l_Lean_mkConst(v___x_2569_, v___x_2547_);
v___x_2571_ = lean_unsigned_to_nat(4u);
v___x_2572_ = lean_mk_empty_array_with_capacity(v___x_2571_);
v___x_2573_ = lean_array_push(v___x_2572_, v_a_2539_);
lean_inc_ref(v_expr_2531_);
v___x_2574_ = lean_array_push(v___x_2573_, v_expr_2531_);
lean_inc_ref(v_expectedType_2532_);
v___x_2575_ = lean_array_push(v___x_2574_, v_expectedType_2532_);
v___x_2576_ = lean_array_push(v___x_2575_, v_a_2565_);
v___x_2577_ = l_Lean_mkAppN(v___x_2570_, v___x_2576_);
lean_dec_ref(v___x_2576_);
v___x_2578_ = l_Lean_Meta_expandCoe(v___x_2577_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2640_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2640_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2640_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v_fst_2590_; lean_object* v___x_2591_; 
v_fst_2590_ = lean_ctor_get(v_a_2579_, 0);
lean_inc(v_a_2536_);
lean_inc_ref(v_a_2535_);
lean_inc(v_a_2534_);
lean_inc_ref(v_a_2533_);
lean_inc(v_fst_2590_);
v___x_2591_ = lean_infer_type(v_fst_2590_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2591_);
lean_inc_ref(v_expectedType_2532_);
v___x_2593_ = l_Lean_Meta_isExprDefEq(v_a_2592_, v_expectedType_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; uint8_t v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref(v___x_2593_);
v___x_2595_ = lean_unbox(v_a_2594_);
lean_dec(v_a_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2621_; 
lean_inc(v_fst_2590_);
lean_del_object(v___x_2581_);
lean_del_object(v___x_2567_);
v_isSharedCheck_2621_ = !lean_is_exclusive(v_a_2579_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; lean_object* v_unused_2623_; 
v_unused_2622_ = lean_ctor_get(v_a_2579_, 1);
lean_dec(v_unused_2622_);
v_unused_2623_ = lean_ctor_get(v_a_2579_, 0);
lean_dec(v_unused_2623_);
v___x_2597_ = v_a_2579_;
v_isShared_2598_ = v_isSharedCheck_2621_;
goto v_resetjp_2596_;
}
else
{
lean_dec(v_a_2579_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2621_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2599_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2600_ = l_Lean_indentExpr(v_expr_2531_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set_tag(v___x_2597_, 7);
lean_ctor_set(v___x_2597_, 1, v___x_2600_);
lean_ctor_set(v___x_2597_, 0, v___x_2599_);
v___x_2602_ = v___x_2597_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
v___x_2603_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = l_Lean_indentExpr(v_expectedType_2532_);
v___x_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = l_Lean_indentExpr(v_fst_2590_);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2610_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
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
}
else
{
lean_dec_ref(v_expectedType_2532_);
lean_dec_ref(v_expr_2531_);
goto v___jp_2583_;
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_del_object(v___x_2581_);
lean_dec(v_a_2579_);
lean_del_object(v___x_2567_);
lean_dec_ref(v_expectedType_2532_);
lean_dec_ref(v_expr_2531_);
v_a_2624_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2593_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2593_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_del_object(v___x_2581_);
lean_dec(v_a_2579_);
lean_del_object(v___x_2567_);
lean_dec_ref(v_expectedType_2532_);
lean_dec_ref(v_expr_2531_);
v_a_2632_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2591_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2591_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
v___jp_2583_:
{
lean_object* v___x_2585_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v_a_2579_);
v___x_2585_ = v___x_2567_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2579_);
v___x_2585_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2587_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2585_);
v___x_2587_ = v___x_2581_;
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
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_del_object(v___x_2567_);
lean_dec_ref(v_expectedType_2532_);
lean_dec_ref(v_expr_2531_);
v_a_2641_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2578_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2578_);
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
default: 
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
lean_dec_ref(v___x_2547_);
lean_dec(v_a_2539_);
lean_dec_ref(v_expectedType_2532_);
lean_dec_ref(v_expr_2531_);
v___x_2650_ = lean_box(2);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2650_);
v___x_2652_ = v___x_2559_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
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
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec_ref(v___x_2547_);
lean_dec(v_a_2539_);
lean_dec_ref(v_expectedType_2532_);
lean_dec_ref(v_expr_2531_);
v_a_2655_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2556_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2556_);
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
lean_dec(v_a_2541_);
lean_dec(v_a_2539_);
lean_dec_ref(v_expectedType_2532_);
lean_dec_ref(v_expr_2531_);
v_a_2663_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2542_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2542_);
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
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec(v_a_2539_);
lean_dec_ref(v_expectedType_2532_);
lean_dec_ref(v_expr_2531_);
v_a_2671_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2540_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2540_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
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
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec_ref(v_expectedType_2532_);
lean_dec_ref(v_expr_2531_);
v_a_2679_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2538_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2538_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2687_, lean_object* v_expectedType_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2687_, v_expectedType_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2695_, lean_object* v_msg_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2703_, lean_object* v_msg_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2703_, v_msg_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2711_, lean_object* v_expectedType_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2711_, v_expectedType_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2743_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2743_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2743_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
switch(lean_obj_tag(v_a_2719_))
{
case 0:
{
lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2723_ = lean_box(0);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v___x_2723_);
v___x_2725_ = v___x_2721_;
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
case 1:
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2738_; 
v_a_2727_ = lean_ctor_get(v_a_2719_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_a_2719_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2729_ = v_a_2719_;
v_isShared_2730_ = v_isSharedCheck_2738_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v_a_2719_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2738_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v_fst_2731_; lean_object* v___x_2733_; 
v_fst_2731_ = lean_ctor_get(v_a_2727_, 0);
lean_inc(v_fst_2731_);
lean_dec(v_a_2727_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v_fst_2731_);
v___x_2733_ = v___x_2729_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_fst_2731_);
v___x_2733_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2735_; 
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v___x_2733_);
v___x_2735_ = v___x_2721_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
default: 
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = lean_box(2);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v___x_2739_);
v___x_2741_ = v___x_2721_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
v_a_2744_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2718_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2718_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2752_, lean_object* v_expectedType_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2752_, v_expectedType_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
return v_res_2759_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2768_ = l_Lean_stringToMessageData(v___x_2767_);
return v___x_2768_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2771_ = l_Lean_stringToMessageData(v___x_2770_);
return v___x_2771_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2774_ = l_Lean_stringToMessageData(v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2781_; 
lean_inc(v_a_2779_);
lean_inc_ref(v_a_2778_);
lean_inc(v_a_2777_);
lean_inc_ref(v_a_2776_);
lean_inc_ref(v_expr_2775_);
v___x_2781_ = lean_infer_type(v_expr_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc_n(v_a_2782_, 2);
lean_dec_ref(v___x_2781_);
v___x_2783_ = l_Lean_Meta_getLevel(v_a_2782_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref(v___x_2783_);
v___x_2785_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc_n(v_a_2786_, 2);
lean_dec_ref(v___x_2785_);
v___x_2787_ = l_Lean_mkSort(v_a_2786_);
lean_inc(v_a_2782_);
v___x_2788_ = l_Lean_mkArrow(v_a_2782_, v___x_2787_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref(v___x_2788_);
v___x_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_a_2789_);
v___x_2791_ = 0;
v___x_2792_ = lean_box(0);
v___x_2793_ = l_Lean_Meta_mkFreshExprMVar(v___x_2790_, v___x_2791_, v___x_2792_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc_n(v_a_2794_, 2);
lean_dec_ref(v___x_2793_);
v___x_2795_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_a_2786_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2798_, 0, v_a_2784_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
lean_inc_ref(v___x_2798_);
v___x_2799_ = l_Lean_Expr_const___override(v___x_2795_, v___x_2798_);
lean_inc(v_a_2782_);
v___x_2800_ = l_Lean_mkAppB(v___x_2799_, v_a_2782_, v_a_2794_);
v___x_2801_ = lean_box(0);
v___x_2802_ = l_Lean_Meta_trySynthInstance(v___x_2800_, v___x_2801_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2889_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2889_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2889_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
if (lean_obj_tag(v_a_2803_) == 1)
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2885_; 
lean_del_object(v___x_2805_);
v_a_2807_ = lean_ctor_get(v_a_2803_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_a_2803_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2809_ = v_a_2803_;
v_isShared_2810_ = v_isSharedCheck_2885_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v_a_2803_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2885_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2811_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2812_ = l_Lean_Expr_const___override(v___x_2811_, v___x_2798_);
lean_inc_ref(v_expr_2775_);
lean_inc(v_a_2807_);
v___x_2813_ = l_Lean_mkApp4(v___x_2812_, v_a_2782_, v_a_2794_, v_a_2807_, v_expr_2775_);
v___x_2814_ = l_Lean_Meta_expandCoe(v___x_2813_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2876_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2876_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2876_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_fst_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2874_; 
v_fst_2819_ = lean_ctor_get(v_a_2815_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_a_2815_);
if (v_isSharedCheck_2874_ == 0)
{
lean_object* v_unused_2875_; 
v_unused_2875_ = lean_ctor_get(v_a_2815_, 1);
lean_dec(v_unused_2875_);
v___x_2821_ = v_a_2815_;
v_isShared_2822_ = v_isSharedCheck_2874_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_fst_2819_);
lean_dec(v_a_2815_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2874_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2830_; 
lean_inc(v_a_2779_);
lean_inc_ref(v_a_2778_);
lean_inc(v_a_2777_);
lean_inc_ref(v_a_2776_);
lean_inc(v_fst_2819_);
v___x_2830_ = lean_infer_type(v_fst_2819_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___x_2830_);
lean_inc(v_a_2779_);
lean_inc_ref(v_a_2778_);
lean_inc(v_a_2777_);
lean_inc_ref(v_a_2776_);
v___x_2832_ = lean_whnf(v_a_2831_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; uint8_t v___x_2834_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref(v___x_2832_);
v___x_2834_ = l_Lean_Expr_isForall(v_a_2833_);
lean_dec(v_a_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
lean_del_object(v___x_2817_);
lean_del_object(v___x_2809_);
v___x_2835_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2836_ = l_Lean_indentExpr(v_expr_2775_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 7);
lean_ctor_set(v___x_2821_, 1, v___x_2836_);
lean_ctor_set(v___x_2821_, 0, v___x_2835_);
v___x_2838_ = v___x_2821_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
v___x_2839_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = l_Lean_indentExpr(v_fst_2819_);
v___x_2842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2840_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2844_ = l_Lean_indentExpr(v_a_2807_);
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = l_Lean_MessageData_hint_x27(v___x_2845_);
v___x_2847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2842_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
v___x_2848_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2847_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_del_object(v___x_2821_);
lean_dec(v_a_2807_);
lean_dec_ref(v_expr_2775_);
goto v___jp_2823_;
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_del_object(v___x_2821_);
lean_dec(v_fst_2819_);
lean_del_object(v___x_2817_);
lean_del_object(v___x_2809_);
lean_dec(v_a_2807_);
lean_dec_ref(v_expr_2775_);
v_a_2858_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2832_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2832_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_del_object(v___x_2821_);
lean_dec(v_fst_2819_);
lean_del_object(v___x_2817_);
lean_del_object(v___x_2809_);
lean_dec(v_a_2807_);
lean_dec_ref(v_expr_2775_);
v_a_2866_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2830_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2830_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
v___jp_2823_:
{
lean_object* v___x_2825_; 
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v_fst_2819_);
v___x_2825_ = v___x_2809_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_fst_2819_);
v___x_2825_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2827_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2825_);
v___x_2827_ = v___x_2817_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_del_object(v___x_2809_);
lean_dec(v_a_2807_);
lean_dec_ref(v_expr_2775_);
v_a_2877_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2814_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2814_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
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
lean_object* v___x_2887_; 
lean_dec(v_a_2803_);
lean_dec_ref(v___x_2798_);
lean_dec(v_a_2794_);
lean_dec(v_a_2782_);
lean_dec_ref(v_expr_2775_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2801_);
v___x_2887_ = v___x_2805_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2801_);
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
lean_dec_ref(v___x_2798_);
lean_dec(v_a_2794_);
lean_dec(v_a_2782_);
lean_dec_ref(v_expr_2775_);
v_a_2890_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2802_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2802_);
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
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
lean_dec(v_a_2782_);
lean_dec_ref(v_expr_2775_);
v_a_2898_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2793_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2793_);
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
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
lean_dec(v_a_2782_);
lean_dec_ref(v_expr_2775_);
v_a_2906_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2788_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2788_);
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
lean_dec(v_a_2784_);
lean_dec(v_a_2782_);
lean_dec_ref(v_expr_2775_);
v_a_2914_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2785_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2785_);
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
lean_dec(v_a_2782_);
lean_dec_ref(v_expr_2775_);
v_a_2922_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2783_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2783_);
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
lean_dec_ref(v_expr_2775_);
v_a_2930_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2781_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2781_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
return v_res_2944_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
return v___x_2953_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2956_ = l_Lean_stringToMessageData(v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___x_2963_; 
lean_inc(v_a_2961_);
lean_inc_ref(v_a_2960_);
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc_ref(v_expr_2957_);
v___x_2963_ = lean_infer_type(v_expr_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc_n(v_a_2964_, 2);
lean_dec_ref(v___x_2963_);
v___x_2965_ = l_Lean_Meta_getLevel(v_a_2964_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2967_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___x_2965_);
v___x_2967_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc_n(v_a_2968_, 2);
lean_dec_ref(v___x_2967_);
v___x_2969_ = l_Lean_mkSort(v_a_2968_);
v___x_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
v___x_2971_ = 0;
v___x_2972_ = lean_box(0);
v___x_2973_ = l_Lean_Meta_mkFreshExprMVar(v___x_2970_, v___x_2971_, v___x_2972_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc_n(v_a_2974_, 2);
lean_dec_ref(v___x_2973_);
v___x_2975_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_2976_ = lean_box(0);
v___x_2977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2977_, 0, v_a_2968_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2978_, 0, v_a_2966_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
lean_inc_ref(v___x_2978_);
v___x_2979_ = l_Lean_Expr_const___override(v___x_2975_, v___x_2978_);
lean_inc(v_a_2964_);
v___x_2980_ = l_Lean_mkAppB(v___x_2979_, v_a_2964_, v_a_2974_);
v___x_2981_ = lean_box(0);
v___x_2982_ = l_Lean_Meta_trySynthInstance(v___x_2980_, v___x_2981_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3069_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_3069_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3069_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
if (lean_obj_tag(v_a_2983_) == 1)
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3065_; 
lean_del_object(v___x_2985_);
v_a_2987_ = lean_ctor_get(v_a_2983_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_a_2983_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_2989_ = v_a_2983_;
v_isShared_2990_ = v_isSharedCheck_3065_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v_a_2983_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3065_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2991_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_2992_ = l_Lean_Expr_const___override(v___x_2991_, v___x_2978_);
lean_inc_ref(v_expr_2957_);
lean_inc(v_a_2987_);
v___x_2993_ = l_Lean_mkApp4(v___x_2992_, v_a_2964_, v_a_2974_, v_a_2987_, v_expr_2957_);
v___x_2994_ = l_Lean_Meta_expandCoe(v___x_2993_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3056_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3056_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3056_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v_fst_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3054_; 
v_fst_2999_ = lean_ctor_get(v_a_2995_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_a_2995_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; 
v_unused_3055_ = lean_ctor_get(v_a_2995_, 1);
lean_dec(v_unused_3055_);
v___x_3001_ = v_a_2995_;
v_isShared_3002_ = v_isSharedCheck_3054_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_fst_2999_);
lean_dec(v_a_2995_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3054_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3010_; 
lean_inc(v_a_2961_);
lean_inc_ref(v_a_2960_);
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc(v_fst_2999_);
v___x_3010_ = lean_infer_type(v_fst_2999_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
lean_inc(v_a_2961_);
lean_inc_ref(v_a_2960_);
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
v___x_3012_ = lean_whnf(v_a_3011_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; uint8_t v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref(v___x_3012_);
v___x_3014_ = l_Lean_Expr_isSort(v_a_3013_);
lean_dec(v_a_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
lean_del_object(v___x_2997_);
lean_del_object(v___x_2989_);
v___x_3015_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3016_ = l_Lean_indentExpr(v_expr_2957_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 7);
lean_ctor_set(v___x_3001_, 1, v___x_3016_);
lean_ctor_set(v___x_3001_, 0, v___x_3015_);
v___x_3018_ = v___x_3001_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3015_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
v___x_3019_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3018_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = l_Lean_indentExpr(v_fst_2999_);
v___x_3022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3024_ = l_Lean_indentExpr(v_a_2987_);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l_Lean_MessageData_hint_x27(v___x_3025_);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3022_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3027_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
else
{
lean_del_object(v___x_3001_);
lean_dec(v_a_2987_);
lean_dec_ref(v_expr_2957_);
goto v___jp_3003_;
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_del_object(v___x_3001_);
lean_dec(v_fst_2999_);
lean_del_object(v___x_2997_);
lean_del_object(v___x_2989_);
lean_dec(v_a_2987_);
lean_dec_ref(v_expr_2957_);
v_a_3038_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3012_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3012_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_del_object(v___x_3001_);
lean_dec(v_fst_2999_);
lean_del_object(v___x_2997_);
lean_del_object(v___x_2989_);
lean_dec(v_a_2987_);
lean_dec_ref(v_expr_2957_);
v_a_3046_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3010_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3010_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
v___jp_3003_:
{
lean_object* v___x_3005_; 
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v_fst_2999_);
v___x_3005_ = v___x_2989_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_fst_2999_);
v___x_3005_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3007_; 
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3005_);
v___x_3007_ = v___x_2997_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_del_object(v___x_2989_);
lean_dec(v_a_2987_);
lean_dec_ref(v_expr_2957_);
v_a_3057_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_2994_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_2994_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
else
{
lean_object* v___x_3067_; 
lean_dec(v_a_2983_);
lean_dec_ref(v___x_2978_);
lean_dec(v_a_2974_);
lean_dec(v_a_2964_);
lean_dec_ref(v_expr_2957_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2981_);
v___x_3067_ = v___x_2985_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_2981_);
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
lean_dec_ref(v___x_2978_);
lean_dec(v_a_2974_);
lean_dec(v_a_2964_);
lean_dec_ref(v_expr_2957_);
v_a_3070_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_2982_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_2982_);
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
lean_dec(v_a_2968_);
lean_dec(v_a_2966_);
lean_dec(v_a_2964_);
lean_dec_ref(v_expr_2957_);
v_a_3078_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_2973_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_2973_);
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
lean_dec(v_a_2966_);
lean_dec(v_a_2964_);
lean_dec_ref(v_expr_2957_);
v_a_3086_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_2967_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_2967_);
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
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v_a_2964_);
lean_dec_ref(v_expr_2957_);
v_a_3094_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_2965_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_2965_);
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
lean_dec_ref(v_expr_2957_);
v_a_3102_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_2963_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_2963_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
lean_dec(v_a_3114_);
lean_dec_ref(v_a_3113_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3117_, lean_object* v___y_3118_){
_start:
{
uint8_t v___x_3120_; 
v___x_3120_ = l_Lean_Expr_hasMVar(v_e_3117_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_e_3117_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; lean_object* v_mctx_3123_; lean_object* v___x_3124_; lean_object* v_fst_3125_; lean_object* v_snd_3126_; lean_object* v___x_3127_; lean_object* v_cache_3128_; lean_object* v_zetaDeltaFVarIds_3129_; lean_object* v_postponed_3130_; lean_object* v_diag_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3140_; 
v___x_3122_ = lean_st_ref_get(v___y_3118_);
v_mctx_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc_ref(v_mctx_3123_);
lean_dec(v___x_3122_);
v___x_3124_ = l_Lean_instantiateMVarsCore(v_mctx_3123_, v_e_3117_);
v_fst_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_fst_3125_);
v_snd_3126_ = lean_ctor_get(v___x_3124_, 1);
lean_inc(v_snd_3126_);
lean_dec_ref(v___x_3124_);
v___x_3127_ = lean_st_ref_take(v___y_3118_);
v_cache_3128_ = lean_ctor_get(v___x_3127_, 1);
v_zetaDeltaFVarIds_3129_ = lean_ctor_get(v___x_3127_, 2);
v_postponed_3130_ = lean_ctor_get(v___x_3127_, 3);
v_diag_3131_ = lean_ctor_get(v___x_3127_, 4);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v___x_3127_, 0);
lean_dec(v_unused_3141_);
v___x_3133_ = v___x_3127_;
v_isShared_3134_ = v_isSharedCheck_3140_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_diag_3131_);
lean_inc(v_postponed_3130_);
lean_inc(v_zetaDeltaFVarIds_3129_);
lean_inc(v_cache_3128_);
lean_dec(v___x_3127_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3140_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v_snd_3126_);
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_snd_3126_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_cache_3128_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_zetaDeltaFVarIds_3129_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v_postponed_3130_);
lean_ctor_set(v_reuseFailAlloc_3139_, 4, v_diag_3131_);
v___x_3136_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_st_ref_set(v___y_3118_, v___x_3136_);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_fst_3125_);
return v___x_3138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3142_, v___y_3143_);
lean_dec(v___y_3143_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3146_, v___y_3148_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
return v_res_3159_;
}
}
static uint64_t _init_l_Lean_Meta_isTypeApp_x3f___closed__0(void){
_start:
{
uint8_t v___x_3160_; uint64_t v___x_3161_; 
v___x_3160_ = 2;
v___x_3161_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v___x_3168_; uint8_t v_foApprox_3169_; uint8_t v_ctxApprox_3170_; uint8_t v_quasiPatternApprox_3171_; uint8_t v_constApprox_3172_; uint8_t v_isDefEqStuckEx_3173_; uint8_t v_unificationHints_3174_; uint8_t v_proofIrrelevance_3175_; uint8_t v_assignSyntheticOpaque_3176_; uint8_t v_offsetCnstrs_3177_; uint8_t v_etaStruct_3178_; uint8_t v_univApprox_3179_; uint8_t v_iota_3180_; uint8_t v_beta_3181_; uint8_t v_proj_3182_; uint8_t v_zeta_3183_; uint8_t v_zetaDelta_3184_; uint8_t v_zetaUnused_3185_; uint8_t v_zetaHave_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3251_; 
v___x_3168_ = l_Lean_Meta_Context_config(v_a_3163_);
v_foApprox_3169_ = lean_ctor_get_uint8(v___x_3168_, 0);
v_ctxApprox_3170_ = lean_ctor_get_uint8(v___x_3168_, 1);
v_quasiPatternApprox_3171_ = lean_ctor_get_uint8(v___x_3168_, 2);
v_constApprox_3172_ = lean_ctor_get_uint8(v___x_3168_, 3);
v_isDefEqStuckEx_3173_ = lean_ctor_get_uint8(v___x_3168_, 4);
v_unificationHints_3174_ = lean_ctor_get_uint8(v___x_3168_, 5);
v_proofIrrelevance_3175_ = lean_ctor_get_uint8(v___x_3168_, 6);
v_assignSyntheticOpaque_3176_ = lean_ctor_get_uint8(v___x_3168_, 7);
v_offsetCnstrs_3177_ = lean_ctor_get_uint8(v___x_3168_, 8);
v_etaStruct_3178_ = lean_ctor_get_uint8(v___x_3168_, 10);
v_univApprox_3179_ = lean_ctor_get_uint8(v___x_3168_, 11);
v_iota_3180_ = lean_ctor_get_uint8(v___x_3168_, 12);
v_beta_3181_ = lean_ctor_get_uint8(v___x_3168_, 13);
v_proj_3182_ = lean_ctor_get_uint8(v___x_3168_, 14);
v_zeta_3183_ = lean_ctor_get_uint8(v___x_3168_, 15);
v_zetaDelta_3184_ = lean_ctor_get_uint8(v___x_3168_, 16);
v_zetaUnused_3185_ = lean_ctor_get_uint8(v___x_3168_, 17);
v_zetaHave_3186_ = lean_ctor_get_uint8(v___x_3168_, 18);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3188_ = v___x_3168_;
v_isShared_3189_ = v_isSharedCheck_3251_;
goto v_resetjp_3187_;
}
else
{
lean_dec(v___x_3168_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3251_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
uint8_t v_trackZetaDelta_3190_; lean_object* v_zetaDeltaSet_3191_; lean_object* v_lctx_3192_; lean_object* v_localInstances_3193_; lean_object* v_defEqCtx_x3f_3194_; lean_object* v_synthPendingDepth_3195_; lean_object* v_canUnfold_x3f_3196_; uint8_t v_univApprox_3197_; uint8_t v_inTypeClassResolution_3198_; uint8_t v_cacheInferType_3199_; uint8_t v___x_3200_; lean_object* v_config_3202_; 
v_trackZetaDelta_3190_ = lean_ctor_get_uint8(v_a_3163_, sizeof(void*)*7);
v_zetaDeltaSet_3191_ = lean_ctor_get(v_a_3163_, 1);
v_lctx_3192_ = lean_ctor_get(v_a_3163_, 2);
v_localInstances_3193_ = lean_ctor_get(v_a_3163_, 3);
v_defEqCtx_x3f_3194_ = lean_ctor_get(v_a_3163_, 4);
v_synthPendingDepth_3195_ = lean_ctor_get(v_a_3163_, 5);
v_canUnfold_x3f_3196_ = lean_ctor_get(v_a_3163_, 6);
v_univApprox_3197_ = lean_ctor_get_uint8(v_a_3163_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3198_ = lean_ctor_get_uint8(v_a_3163_, sizeof(void*)*7 + 2);
v_cacheInferType_3199_ = lean_ctor_get_uint8(v_a_3163_, sizeof(void*)*7 + 3);
v___x_3200_ = 2;
if (v_isShared_3189_ == 0)
{
v_config_3202_ = v___x_3188_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 0, v_foApprox_3169_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 1, v_ctxApprox_3170_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 2, v_quasiPatternApprox_3171_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 3, v_constApprox_3172_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 4, v_isDefEqStuckEx_3173_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 5, v_unificationHints_3174_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 6, v_proofIrrelevance_3175_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 7, v_assignSyntheticOpaque_3176_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 8, v_offsetCnstrs_3177_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 10, v_etaStruct_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 11, v_univApprox_3179_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 12, v_iota_3180_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 13, v_beta_3181_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 14, v_proj_3182_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 15, v_zeta_3183_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 16, v_zetaDelta_3184_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 17, v_zetaUnused_3185_);
lean_ctor_set_uint8(v_reuseFailAlloc_3250_, 18, v_zetaHave_3186_);
v_config_3202_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
uint64_t v___x_3203_; uint64_t v___x_3204_; uint64_t v___x_3205_; uint64_t v___x_3206_; uint64_t v___x_3207_; uint64_t v_key_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_ctor_set_uint8(v_config_3202_, 9, v___x_3200_);
v___x_3203_ = l_Lean_Meta_Context_configKey(v_a_3163_);
v___x_3204_ = 2ULL;
v___x_3205_ = lean_uint64_shift_right(v___x_3203_, v___x_3204_);
v___x_3206_ = lean_uint64_shift_left(v___x_3205_, v___x_3204_);
v___x_3207_ = lean_uint64_once(&l_Lean_Meta_isTypeApp_x3f___closed__0, &l_Lean_Meta_isTypeApp_x3f___closed__0_once, _init_l_Lean_Meta_isTypeApp_x3f___closed__0);
v_key_3208_ = lean_uint64_lor(v___x_3206_, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3209_, 0, v_config_3202_);
lean_ctor_set_uint64(v___x_3209_, sizeof(void*)*1, v_key_3208_);
lean_inc(v_canUnfold_x3f_3196_);
lean_inc(v_synthPendingDepth_3195_);
lean_inc(v_defEqCtx_x3f_3194_);
lean_inc_ref(v_localInstances_3193_);
lean_inc_ref(v_lctx_3192_);
lean_inc(v_zetaDeltaSet_3191_);
v___x_3210_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v_zetaDeltaSet_3191_);
lean_ctor_set(v___x_3210_, 2, v_lctx_3192_);
lean_ctor_set(v___x_3210_, 3, v_localInstances_3193_);
lean_ctor_set(v___x_3210_, 4, v_defEqCtx_x3f_3194_);
lean_ctor_set(v___x_3210_, 5, v_synthPendingDepth_3195_);
lean_ctor_set(v___x_3210_, 6, v_canUnfold_x3f_3196_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*7, v_trackZetaDelta_3190_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*7 + 1, v_univApprox_3197_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3198_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*7 + 3, v_cacheInferType_3199_);
lean_inc(v_a_3166_);
lean_inc_ref(v_a_3165_);
lean_inc(v_a_3164_);
v___x_3211_ = lean_whnf(v_type_3162_, v___x_3210_, v_a_3164_, v_a_3165_, v_a_3166_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3241_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3241_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3241_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
if (lean_obj_tag(v_a_3212_) == 5)
{
lean_object* v_fn_3216_; lean_object* v_arg_3217_; lean_object* v___x_3218_; lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3236_; 
lean_del_object(v___x_3214_);
v_fn_3216_ = lean_ctor_get(v_a_3212_, 0);
lean_inc_ref(v_fn_3216_);
v_arg_3217_ = lean_ctor_get(v_a_3212_, 1);
lean_inc_ref(v_arg_3217_);
lean_dec_ref(v_a_3212_);
v___x_3218_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3216_, v_a_3164_);
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3236_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3236_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3235_; 
v___x_3223_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3217_, v_a_3164_);
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3235_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3235_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3228_, 0, v_a_3219_);
lean_ctor_set(v___x_3228_, 1, v_a_3224_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 0, v___x_3228_);
v___x_3230_ = v___x_3221_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3232_; 
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3230_);
v___x_3232_ = v___x_3226_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
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
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
lean_dec(v_a_3212_);
v___x_3237_ = lean_box(0);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v___x_3237_);
v___x_3239_ = v___x_3214_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
v_a_3242_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3211_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3211_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Meta_isTypeApp_x3f(v_type_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_);
lean_dec(v_a_3256_);
lean_dec_ref(v_a_3255_);
lean_dec(v_a_3254_);
lean_dec_ref(v_a_3253_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_Meta_isTypeApp_x3f(v_type_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3301_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3301_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3301_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
if (lean_obj_tag(v_a_3266_) == 1)
{
lean_object* v_val_3270_; lean_object* v_fst_3271_; lean_object* v___x_3272_; 
lean_del_object(v___x_3268_);
v_val_3270_ = lean_ctor_get(v_a_3266_, 0);
lean_inc(v_val_3270_);
lean_dec_ref(v_a_3266_);
v_fst_3271_ = lean_ctor_get(v_val_3270_, 0);
lean_inc(v_fst_3271_);
lean_dec(v_val_3270_);
v___x_3272_ = l_Lean_Meta_isMonad_x3f(v_fst_3271_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3287_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3287_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3287_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
if (lean_obj_tag(v_a_3273_) == 0)
{
uint8_t v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3277_ = 0;
v___x_3278_ = lean_box(v___x_3277_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v___x_3278_);
v___x_3280_ = v___x_3275_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
else
{
uint8_t v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3285_; 
lean_dec_ref(v_a_3273_);
v___x_3282_ = 1;
v___x_3283_ = lean_box(v___x_3282_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v___x_3283_);
v___x_3285_ = v___x_3275_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_a_3288_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3272_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3272_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
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
uint8_t v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3299_; 
lean_dec(v_a_3266_);
v___x_3296_ = 0;
v___x_3297_ = lean_box(v___x_3296_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3297_);
v___x_3299_ = v___x_3268_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
v_a_3302_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3265_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3265_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Meta_isMonadApp(v_type_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
return v_res_3316_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3317_, lean_object* v_opt_3318_){
_start:
{
lean_object* v_name_3319_; lean_object* v_defValue_3320_; lean_object* v_map_3321_; lean_object* v___x_3322_; 
v_name_3319_ = lean_ctor_get(v_opt_3318_, 0);
v_defValue_3320_ = lean_ctor_get(v_opt_3318_, 1);
v_map_3321_ = lean_ctor_get(v_opts_3317_, 0);
v___x_3322_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3321_, v_name_3319_);
if (lean_obj_tag(v___x_3322_) == 0)
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_unbox(v_defValue_3320_);
return v___x_3323_;
}
else
{
lean_object* v_val_3324_; 
v_val_3324_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_val_3324_);
lean_dec_ref(v___x_3322_);
if (lean_obj_tag(v_val_3324_) == 1)
{
uint8_t v_v_3325_; 
v_v_3325_ = lean_ctor_get_uint8(v_val_3324_, 0);
lean_dec_ref(v_val_3324_);
return v_v_3325_;
}
else
{
uint8_t v___x_3326_; 
lean_dec(v_val_3324_);
v___x_3326_ = lean_unbox(v_defValue_3320_);
return v___x_3326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3327_, lean_object* v_opt_3328_){
_start:
{
uint8_t v_res_3329_; lean_object* v_r_3330_; 
v_res_3329_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3327_, v_opt_3328_);
lean_dec_ref(v_opt_3328_);
lean_dec_ref(v_opts_3327_);
v_r_3330_ = lean_box(v_res_3329_);
return v_r_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec_ref(v_x_3341_);
return v_res_3347_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = lean_unsigned_to_nat(0u);
v___x_3358_ = l_Lean_mkBVar(v___x_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3370_, lean_object* v_expectedType_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v___y_3378_; uint8_t v___y_3379_; lean_object* v_a_3384_; lean_object* v___y_3388_; lean_object* v___x_3398_; lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3802_; 
v___x_3398_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3371_, v_a_3373_);
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3802_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3802_;
goto v_resetjp_3400_;
}
v___jp_3377_:
{
if (v___y_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec_ref(v___y_3378_);
v___x_3380_ = lean_box(0);
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
return v___x_3381_;
}
else
{
lean_object* v___x_3382_; 
v___x_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___y_3378_);
return v___x_3382_;
}
}
v___jp_3383_:
{
uint8_t v___x_3385_; 
v___x_3385_ = l_Lean_Exception_isInterrupt(v_a_3384_);
if (v___x_3385_ == 0)
{
uint8_t v___x_3386_; 
lean_inc_ref(v_a_3384_);
v___x_3386_ = l_Lean_Exception_isRuntime(v_a_3384_);
v___y_3378_ = v_a_3384_;
v___y_3379_ = v___x_3386_;
goto v___jp_3377_;
}
else
{
v___y_3378_ = v_a_3384_;
v___y_3379_ = v___x_3385_;
goto v___jp_3377_;
}
}
v___jp_3387_:
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3397_; 
v_a_3389_ = lean_ctor_get(v___y_3388_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___y_3388_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3391_ = v___y_3388_;
v_isShared_3392_ = v_isSharedCheck_3397_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___y_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3397_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_a_3393_; lean_object* v___x_3395_; 
v_a_3393_ = lean_ctor_get(v_a_3389_, 0);
lean_inc(v_a_3393_);
lean_dec(v_a_3389_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v_a_3393_);
v___x_3395_ = v___x_3391_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; 
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc_ref(v_e_3370_);
v___x_3403_ = lean_infer_type(v_e_3370_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3405_; lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3793_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref(v___x_3403_);
v___x_3405_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3404_, v_a_3373_);
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3408_ = v___x_3405_;
v_isShared_3409_ = v_isSharedCheck_3793_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3405_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3793_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; 
lean_inc(v_a_3399_);
v___x_3410_ = l_Lean_Meta_isTypeApp_x3f(v_a_3399_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3784_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3784_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3784_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
if (lean_obj_tag(v_a_3411_) == 1)
{
lean_object* v_val_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3779_; 
lean_del_object(v___x_3413_);
v_val_3415_ = lean_ctor_get(v_a_3411_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_a_3411_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3417_ = v_a_3411_;
v_isShared_3418_ = v_isSharedCheck_3779_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_val_3415_);
lean_dec(v_a_3411_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3779_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v_fst_3419_; lean_object* v_snd_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3778_; 
v_fst_3419_ = lean_ctor_get(v_val_3415_, 0);
v_snd_3420_ = lean_ctor_get(v_val_3415_, 1);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_val_3415_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3422_ = v_val_3415_;
v_isShared_3423_ = v_isSharedCheck_3778_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_snd_3420_);
lean_inc(v_fst_3419_);
lean_dec(v_val_3415_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3778_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; 
lean_inc(v_a_3406_);
v___x_3424_ = l_Lean_Meta_isTypeApp_x3f(v_a_3406_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3769_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3427_ = v___x_3424_;
v_isShared_3428_ = v_isSharedCheck_3769_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3424_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3769_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
if (lean_obj_tag(v_a_3425_) == 1)
{
lean_object* v_val_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3764_; 
lean_del_object(v___x_3427_);
v_val_3429_ = lean_ctor_get(v_a_3425_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_a_3425_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3431_ = v_a_3425_;
v_isShared_3432_ = v_isSharedCheck_3764_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_val_3429_);
lean_dec(v_a_3425_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3764_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_fst_3433_; lean_object* v_snd_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3763_; 
v_fst_3433_ = lean_ctor_get(v_val_3429_, 0);
v_snd_3434_ = lean_ctor_get(v_val_3429_, 1);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_val_3429_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3436_ = v_val_3429_;
v_isShared_3437_ = v_isSharedCheck_3763_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_snd_3434_);
lean_inc(v_fst_3433_);
lean_dec(v_val_3429_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3763_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Lean_Meta_saveState___redArg(v_a_3373_, v_a_3375_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref(v___x_3438_);
lean_inc(v_fst_3419_);
lean_inc(v_fst_3433_);
v___x_3440_ = l_Lean_Meta_isExprDefEq(v_fst_3433_, v_fst_3419_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3746_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3746_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3746_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_unbox(v_a_3441_);
lean_dec(v_a_3441_);
if (v___x_3445_ == 0)
{
lean_object* v_options_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
lean_dec(v_a_3439_);
lean_del_object(v___x_3417_);
lean_del_object(v___x_3408_);
lean_del_object(v___x_3401_);
v_options_3446_ = lean_ctor_get(v_a_3374_, 2);
v___x_3447_ = l_Lean_Meta_autoLift;
v___x_3448_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_options_3446_, v___x_3447_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v___x_3449_ = lean_box(0);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3449_);
v___x_3451_ = v___x_3443_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
else
{
lean_object* v___x_3453_; 
lean_del_object(v___x_3443_);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_fst_3433_);
v___x_3453_ = lean_infer_type(v_fst_3433_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref(v___x_3453_);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
v___x_3455_ = lean_whnf(v_a_3454_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref(v___x_3455_);
if (lean_obj_tag(v_a_3456_) == 7)
{
lean_object* v_binderType_3457_; 
v_binderType_3457_ = lean_ctor_get(v_a_3456_, 1);
if (lean_obj_tag(v_binderType_3457_) == 3)
{
lean_object* v_body_3458_; 
v_body_3458_ = lean_ctor_get(v_a_3456_, 2);
if (lean_obj_tag(v_body_3458_) == 3)
{
lean_object* v_u_3459_; lean_object* v_u_3460_; lean_object* v___x_3461_; 
lean_inc_ref(v_body_3458_);
lean_inc_ref(v_binderType_3457_);
lean_dec_ref(v_a_3456_);
v_u_3459_ = lean_ctor_get(v_binderType_3457_, 0);
lean_inc(v_u_3459_);
lean_dec_ref(v_binderType_3457_);
v_u_3460_ = lean_ctor_get(v_body_3458_, 0);
lean_inc(v_u_3460_);
lean_dec_ref(v_body_3458_);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_fst_3419_);
v___x_3461_ = lean_infer_type(v_fst_3419_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3463_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
v___x_3463_ = lean_whnf(v_a_3462_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref(v___x_3463_);
if (lean_obj_tag(v_a_3464_) == 7)
{
lean_object* v_binderType_3465_; 
v_binderType_3465_ = lean_ctor_get(v_a_3464_, 1);
if (lean_obj_tag(v_binderType_3465_) == 3)
{
lean_object* v_body_3466_; 
v_body_3466_ = lean_ctor_get(v_a_3464_, 2);
if (lean_obj_tag(v_body_3466_) == 3)
{
lean_object* v_u_3467_; lean_object* v_u_3468_; lean_object* v___x_3469_; 
lean_inc_ref(v_body_3466_);
lean_inc_ref(v_binderType_3465_);
lean_dec_ref(v_a_3464_);
v_u_3467_ = lean_ctor_get(v_binderType_3465_, 0);
lean_inc(v_u_3467_);
lean_dec_ref(v_binderType_3465_);
v_u_3468_ = lean_ctor_get(v_body_3466_, 0);
lean_inc(v_u_3468_);
lean_dec_ref(v_body_3466_);
v___x_3469_ = l_Lean_Meta_decLevel(v_u_3459_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3471_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref(v___x_3469_);
v___x_3471_ = l_Lean_Meta_decLevel(v_u_3467_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3473_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref(v___x_3471_);
lean_inc(v_a_3470_);
v___x_3473_ = l_Lean_Meta_isLevelDefEq(v_a_3470_, v_a_3472_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3638_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3638_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3638_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_unbox(v_a_3474_);
lean_dec(v_a_3474_);
if (v___x_3478_ == 1)
{
lean_object* v___x_3479_; 
lean_del_object(v___x_3476_);
v___x_3479_ = l_Lean_Meta_decLevel(v_u_3460_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref(v___x_3479_);
v___x_3481_ = l_Lean_Meta_decLevel(v_u_3468_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref(v___x_3481_);
v___x_3483_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3484_ = lean_box(0);
if (v_isShared_3437_ == 0)
{
lean_ctor_set_tag(v___x_3436_, 1);
lean_ctor_set(v___x_3436_, 1, v___x_3484_);
lean_ctor_set(v___x_3436_, 0, v_a_3482_);
v___x_3486_ = v___x_3436_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3482_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3488_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set_tag(v___x_3422_, 1);
lean_ctor_set(v___x_3422_, 1, v___x_3486_);
lean_ctor_set(v___x_3422_, 0, v_a_3480_);
v___x_3488_ = v___x_3422_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3480_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3489_, 0, v_a_3470_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = l_Lean_Expr_const___override(v___x_3483_, v___x_3489_);
v___x_3491_ = lean_unsigned_to_nat(2u);
v___x_3492_ = lean_mk_empty_array_with_capacity(v___x_3491_);
lean_inc(v_fst_3433_);
v___x_3493_ = lean_array_push(v___x_3492_, v_fst_3433_);
lean_inc(v_fst_3419_);
v___x_3494_ = lean_array_push(v___x_3493_, v_fst_3419_);
v___x_3495_ = l_Lean_mkAppN(v___x_3490_, v___x_3494_);
lean_dec_ref(v___x_3494_);
v___x_3496_ = lean_box(0);
v___x_3497_ = l_Lean_Meta_trySynthInstance(v___x_3495_, v___x_3496_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3628_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3628_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3628_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
if (lean_obj_tag(v_a_3498_) == 1)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; 
lean_del_object(v___x_3500_);
v_a_3502_ = lean_ctor_get(v_a_3498_, 0);
lean_inc(v_a_3502_);
lean_dec_ref(v_a_3498_);
lean_inc(v_snd_3434_);
v___x_3503_ = l_Lean_Meta_getDecLevel(v_snd_3434_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3503_);
v___x_3505_ = l_Lean_Meta_getDecLevel(v_a_3406_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3507_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref(v___x_3505_);
lean_inc(v_a_3399_);
v___x_3507_ = l_Lean_Meta_getDecLevel(v_a_3399_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref(v___x_3507_);
v___x_3509_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3510_, 0, v_a_3508_);
lean_ctor_set(v___x_3510_, 1, v___x_3484_);
v___x_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3511_, 0, v_a_3506_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3512_, 0, v_a_3504_);
lean_ctor_set(v___x_3512_, 1, v___x_3511_);
lean_inc_ref(v___x_3512_);
v___x_3513_ = l_Lean_mkConst(v___x_3509_, v___x_3512_);
v___x_3514_ = lean_unsigned_to_nat(5u);
v___x_3515_ = lean_mk_empty_array_with_capacity(v___x_3514_);
lean_inc(v_fst_3433_);
v___x_3516_ = lean_array_push(v___x_3515_, v_fst_3433_);
lean_inc(v_fst_3419_);
v___x_3517_ = lean_array_push(v___x_3516_, v_fst_3419_);
lean_inc(v_a_3502_);
v___x_3518_ = lean_array_push(v___x_3517_, v_a_3502_);
lean_inc(v_snd_3434_);
v___x_3519_ = lean_array_push(v___x_3518_, v_snd_3434_);
lean_inc_ref(v_e_3370_);
v___x_3520_ = lean_array_push(v___x_3519_, v_e_3370_);
v___x_3521_ = l_Lean_mkAppN(v___x_3513_, v___x_3520_);
lean_dec_ref(v___x_3520_);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc_ref(v___x_3521_);
v___x_3522_ = lean_infer_type(v___x_3521_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3524_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref(v___x_3522_);
lean_inc(v_a_3399_);
v___x_3524_ = l_Lean_Meta_isExprDefEq(v_a_3399_, v_a_3523_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3619_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3527_ = v___x_3524_;
v_isShared_3528_ = v_isSharedCheck_3619_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3619_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
uint8_t v___x_3529_; 
v___x_3529_ = lean_unbox(v_a_3525_);
lean_dec(v_a_3525_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; 
lean_del_object(v___x_3527_);
lean_dec_ref(v___x_3521_);
lean_del_object(v___x_3431_);
lean_inc(v_fst_3419_);
v___x_3530_ = l_Lean_Meta_isMonad_x3f(v_fst_3419_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3611_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3611_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3611_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
if (lean_obj_tag(v_a_3531_) == 1)
{
lean_object* v_val_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3607_; 
lean_del_object(v___x_3533_);
v_val_3535_ = lean_ctor_get(v_a_3531_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v_a_3531_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3537_ = v_a_3531_;
v_isShared_3538_ = v_isSharedCheck_3607_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_val_3535_);
lean_dec(v_a_3531_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3607_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; 
lean_inc(v_snd_3434_);
v___x_3539_ = l_Lean_Meta_getLevel(v_snd_3434_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref(v___x_3539_);
lean_inc(v_snd_3420_);
v___x_3541_ = l_Lean_Meta_getLevel(v_snd_3420_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3541_);
v___x_3543_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3544_ = 0;
v___x_3545_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3546_, 0, v_a_3542_);
lean_ctor_set(v___x_3546_, 1, v___x_3484_);
v___x_3547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3547_, 0, v_a_3540_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = l_Lean_mkConst(v___x_3545_, v___x_3547_);
v___x_3549_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3550_ = lean_unsigned_to_nat(3u);
v___x_3551_ = lean_mk_empty_array_with_capacity(v___x_3550_);
lean_inc_n(v_snd_3434_, 2);
v___x_3552_ = lean_array_push(v___x_3551_, v_snd_3434_);
v___x_3553_ = lean_array_push(v___x_3552_, v___x_3549_);
lean_inc(v_snd_3420_);
v___x_3554_ = lean_array_push(v___x_3553_, v_snd_3420_);
v___x_3555_ = l_Lean_mkAppN(v___x_3548_, v___x_3554_);
lean_dec_ref(v___x_3554_);
v___x_3556_ = l_Lean_mkForall(v___x_3543_, v___x_3544_, v_snd_3434_, v___x_3555_);
v___x_3557_ = l_Lean_Meta_trySynthInstance(v___x_3556_, v___x_3496_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3603_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3560_ = v___x_3557_;
v_isShared_3561_ = v_isSharedCheck_3603_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3557_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3603_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
if (lean_obj_tag(v_a_3558_) == 1)
{
lean_object* v_a_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
lean_del_object(v___x_3560_);
v_a_3562_ = lean_ctor_get(v_a_3558_, 0);
lean_inc(v_a_3562_);
lean_dec_ref(v_a_3558_);
v___x_3563_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3564_ = l_Lean_mkConst(v___x_3563_, v___x_3512_);
v___x_3565_ = lean_unsigned_to_nat(8u);
v___x_3566_ = lean_mk_empty_array_with_capacity(v___x_3565_);
v___x_3567_ = lean_array_push(v___x_3566_, v_fst_3433_);
v___x_3568_ = lean_array_push(v___x_3567_, v_fst_3419_);
v___x_3569_ = lean_array_push(v___x_3568_, v_snd_3434_);
v___x_3570_ = lean_array_push(v___x_3569_, v_snd_3420_);
v___x_3571_ = lean_array_push(v___x_3570_, v_a_3502_);
v___x_3572_ = lean_array_push(v___x_3571_, v_a_3562_);
v___x_3573_ = lean_array_push(v___x_3572_, v_val_3535_);
v___x_3574_ = lean_array_push(v___x_3573_, v_e_3370_);
v___x_3575_ = l_Lean_mkAppN(v___x_3564_, v___x_3574_);
lean_dec_ref(v___x_3574_);
v___x_3576_ = l_Lean_Meta_expandCoe(v___x_3575_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v_fst_3578_; lean_object* v___x_3579_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref(v___x_3576_);
v_fst_3578_ = lean_ctor_get(v_a_3577_, 0);
lean_inc_n(v_fst_3578_, 2);
lean_dec(v_a_3577_);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
v___x_3579_ = lean_infer_type(v_fst_3578_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3581_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref(v___x_3579_);
v___x_3581_ = l_Lean_Meta_isExprDefEq(v_a_3399_, v_a_3580_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3596_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3596_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3596_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_unbox(v_a_3582_);
lean_dec(v_a_3582_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3588_; 
lean_dec(v_fst_3578_);
lean_del_object(v___x_3537_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3496_);
v___x_3588_ = v___x_3584_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3496_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
else
{
lean_object* v___x_3591_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v_fst_3578_);
v___x_3591_ = v___x_3537_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_fst_3578_);
v___x_3591_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3593_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3591_);
v___x_3593_ = v___x_3584_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3591_);
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
}
else
{
lean_object* v_a_3597_; 
lean_dec(v_fst_3578_);
lean_del_object(v___x_3537_);
v_a_3597_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3597_);
lean_dec_ref(v___x_3581_);
v_a_3384_ = v_a_3597_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3598_; 
lean_dec(v_fst_3578_);
lean_del_object(v___x_3537_);
lean_dec(v_a_3399_);
v_a_3598_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3598_);
lean_dec_ref(v___x_3579_);
v_a_3384_ = v_a_3598_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3599_; 
lean_del_object(v___x_3537_);
lean_dec(v_a_3399_);
v_a_3599_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3599_);
lean_dec_ref(v___x_3576_);
v_a_3384_ = v_a_3599_;
goto v___jp_3383_;
}
}
else
{
lean_object* v___x_3601_; 
lean_dec(v_a_3558_);
lean_del_object(v___x_3537_);
lean_dec(v_val_3535_);
lean_dec_ref(v___x_3512_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3496_);
v___x_3601_ = v___x_3560_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3496_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
else
{
lean_object* v_a_3604_; 
lean_del_object(v___x_3537_);
lean_dec(v_val_3535_);
lean_dec_ref(v___x_3512_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3604_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3557_);
v_a_3384_ = v_a_3604_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3605_; 
lean_dec(v_a_3540_);
lean_del_object(v___x_3537_);
lean_dec(v_val_3535_);
lean_dec_ref(v___x_3512_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3605_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3605_);
lean_dec_ref(v___x_3541_);
v_a_3384_ = v_a_3605_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3606_; 
lean_del_object(v___x_3537_);
lean_dec(v_val_3535_);
lean_dec_ref(v___x_3512_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3606_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3539_);
v_a_3384_ = v_a_3606_;
goto v___jp_3383_;
}
}
}
else
{
lean_object* v___x_3609_; 
lean_dec(v_a_3531_);
lean_dec_ref(v___x_3512_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3496_);
v___x_3609_ = v___x_3533_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3496_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
else
{
lean_object* v_a_3612_; 
lean_dec_ref(v___x_3512_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3612_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3612_);
lean_dec_ref(v___x_3530_);
v_a_3384_ = v_a_3612_;
goto v___jp_3383_;
}
}
else
{
lean_object* v___x_3614_; 
lean_dec_ref(v___x_3512_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3521_);
v___x_3614_ = v___x_3431_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3521_);
v___x_3614_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3616_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v___x_3614_);
v___x_3616_ = v___x_3527_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
else
{
lean_object* v_a_3620_; 
lean_dec_ref(v___x_3521_);
lean_dec_ref(v___x_3512_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3620_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3620_);
lean_dec_ref(v___x_3524_);
v_a_3384_ = v_a_3620_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3621_; 
lean_dec_ref(v___x_3521_);
lean_dec_ref(v___x_3512_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3621_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3621_);
lean_dec_ref(v___x_3522_);
v_a_3384_ = v_a_3621_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3622_; 
lean_dec(v_a_3506_);
lean_dec(v_a_3504_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3622_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3622_);
lean_dec_ref(v___x_3507_);
v_a_3384_ = v_a_3622_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3623_; 
lean_dec(v_a_3504_);
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3623_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3623_);
lean_dec_ref(v___x_3505_);
v_a_3384_ = v_a_3623_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3624_; 
lean_dec(v_a_3502_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3624_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3624_);
lean_dec_ref(v___x_3503_);
v_a_3384_ = v_a_3624_;
goto v___jp_3383_;
}
}
else
{
lean_object* v___x_3626_; 
lean_dec(v_a_3498_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v___x_3496_);
v___x_3626_ = v___x_3500_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3496_);
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
lean_object* v_a_3629_; 
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3629_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3629_);
lean_dec_ref(v___x_3497_);
v_a_3384_ = v_a_3629_;
goto v___jp_3383_;
}
}
}
}
else
{
lean_object* v_a_3632_; 
lean_dec(v_a_3480_);
lean_dec(v_a_3470_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3632_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3632_);
lean_dec_ref(v___x_3481_);
v_a_3384_ = v_a_3632_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3633_; 
lean_dec(v_a_3470_);
lean_dec(v_u_3468_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3633_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3633_);
lean_dec_ref(v___x_3479_);
v_a_3384_ = v_a_3633_;
goto v___jp_3383_;
}
}
else
{
lean_object* v___x_3634_; lean_object* v___x_3636_; 
lean_dec(v_a_3470_);
lean_dec(v_u_3468_);
lean_dec(v_u_3460_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v___x_3634_ = lean_box(0);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3634_);
v___x_3636_ = v___x_3476_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3634_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_object* v_a_3639_; 
lean_dec(v_a_3470_);
lean_dec(v_u_3468_);
lean_dec(v_u_3460_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3639_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3639_);
lean_dec_ref(v___x_3473_);
v_a_3384_ = v_a_3639_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3640_; 
lean_dec(v_a_3470_);
lean_dec(v_u_3468_);
lean_dec(v_u_3460_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3640_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3640_);
lean_dec_ref(v___x_3471_);
v_a_3384_ = v_a_3640_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3641_; 
lean_dec(v_u_3468_);
lean_dec(v_u_3467_);
lean_dec(v_u_3460_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3641_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3641_);
lean_dec_ref(v___x_3469_);
v_a_3384_ = v_a_3641_;
goto v___jp_3383_;
}
}
else
{
lean_object* v___x_3642_; 
lean_dec(v_u_3460_);
lean_dec(v_u_3459_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v___x_3642_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3464_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec_ref(v_a_3464_);
v___y_3388_ = v___x_3642_;
goto v___jp_3387_;
}
}
else
{
lean_object* v___x_3643_; 
lean_dec(v_u_3460_);
lean_dec(v_u_3459_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v___x_3643_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3464_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec_ref(v_a_3464_);
v___y_3388_ = v___x_3643_;
goto v___jp_3387_;
}
}
else
{
lean_object* v___x_3644_; 
lean_dec(v_u_3460_);
lean_dec(v_u_3459_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v___x_3644_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3464_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec(v_a_3464_);
v___y_3388_ = v___x_3644_;
goto v___jp_3387_;
}
}
else
{
lean_object* v_a_3645_; 
lean_dec(v_u_3460_);
lean_dec(v_u_3459_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3645_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___x_3463_);
v_a_3384_ = v_a_3645_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3646_; 
lean_dec(v_u_3460_);
lean_dec(v_u_3459_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3646_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3646_);
lean_dec_ref(v___x_3461_);
v_a_3384_ = v_a_3646_;
goto v___jp_3383_;
}
}
else
{
lean_object* v___x_3647_; 
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v___x_3647_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3456_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec_ref(v_a_3456_);
v___y_3388_ = v___x_3647_;
goto v___jp_3387_;
}
}
else
{
lean_object* v___x_3648_; 
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v___x_3648_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3456_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec_ref(v_a_3456_);
v___y_3388_ = v___x_3648_;
goto v___jp_3387_;
}
}
else
{
lean_object* v___x_3649_; 
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v___x_3649_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3456_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec(v_a_3456_);
v___y_3388_ = v___x_3649_;
goto v___jp_3387_;
}
}
else
{
lean_object* v_a_3650_; 
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3650_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3650_);
lean_dec_ref(v___x_3455_);
v_a_3384_ = v_a_3650_;
goto v___jp_3383_;
}
}
else
{
lean_object* v_a_3651_; 
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3651_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3651_);
lean_dec_ref(v___x_3453_);
v_a_3384_ = v_a_3651_;
goto v___jp_3383_;
}
}
}
else
{
lean_object* v___x_3652_; 
lean_del_object(v___x_3443_);
lean_del_object(v___x_3436_);
lean_del_object(v___x_3422_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
v___x_3652_ = l_Lean_Meta_isMonad_x3f(v_fst_3419_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3745_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3745_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3745_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
if (lean_obj_tag(v_a_3653_) == 1)
{
lean_object* v___x_3657_; lean_object* v___x_3659_; 
v___x_3657_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v_fst_3433_);
v___x_3659_ = v___x_3431_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_fst_3433_);
v___x_3659_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3661_; 
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v_snd_3434_);
v___x_3661_ = v___x_3417_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_snd_3434_);
v___x_3661_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set_tag(v___x_3408_, 1);
lean_ctor_set(v___x_3408_, 0, v_snd_3420_);
v___x_3663_ = v___x_3408_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_snd_3420_);
v___x_3663_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___y_3666_; uint8_t v___y_3667_; lean_object* v_a_3689_; lean_object* v___x_3693_; 
v___x_3664_ = lean_box(0);
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 1);
lean_ctor_set(v___x_3401_, 0, v_e_3370_);
v___x_3693_ = v___x_3401_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_e_3370_);
v___x_3693_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3692_;
}
v___jp_3665_:
{
if (v___y_3667_ == 0)
{
lean_object* v___x_3668_; 
lean_dec_ref(v___y_3666_);
lean_del_object(v___x_3655_);
v___x_3668_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3439_, v_a_3373_, v_a_3375_);
lean_dec(v_a_3439_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v___x_3668_, 0);
lean_dec(v_unused_3676_);
v___x_3670_ = v___x_3668_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_dec(v___x_3668_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3664_);
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3664_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
v_a_3677_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3668_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3668_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
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
lean_object* v___x_3686_; 
lean_dec(v_a_3439_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 1);
lean_ctor_set(v___x_3655_, 0, v___y_3666_);
v___x_3686_ = v___x_3655_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___y_3666_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
v___jp_3688_:
{
uint8_t v___x_3690_; 
v___x_3690_ = l_Lean_Exception_isInterrupt(v_a_3689_);
if (v___x_3690_ == 0)
{
uint8_t v___x_3691_; 
lean_inc_ref(v_a_3689_);
v___x_3691_ = l_Lean_Exception_isRuntime(v_a_3689_);
v___y_3666_ = v_a_3689_;
v___y_3667_ = v___x_3691_;
goto v___jp_3665_;
}
else
{
v___y_3666_ = v_a_3689_;
v___y_3667_ = v___x_3690_;
goto v___jp_3665_;
}
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3694_ = lean_unsigned_to_nat(6u);
v___x_3695_ = lean_mk_empty_array_with_capacity(v___x_3694_);
v___x_3696_ = lean_array_push(v___x_3695_, v___x_3659_);
v___x_3697_ = lean_array_push(v___x_3696_, v___x_3661_);
v___x_3698_ = lean_array_push(v___x_3697_, v___x_3663_);
v___x_3699_ = lean_array_push(v___x_3698_, v___x_3664_);
v___x_3700_ = lean_array_push(v___x_3699_, v_a_3653_);
v___x_3701_ = lean_array_push(v___x_3700_, v___x_3693_);
v___x_3702_ = l_Lean_Meta_mkAppOptM(v___x_3657_, v___x_3701_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3721_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3705_ = v___x_3702_;
v_isShared_3706_ = v_isSharedCheck_3721_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3702_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3721_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_Meta_expandCoe(v_a_3703_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3719_; 
lean_del_object(v___x_3655_);
lean_dec(v_a_3439_);
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3710_ = v___x_3707_;
v_isShared_3711_ = v_isSharedCheck_3719_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3719_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v_fst_3712_; lean_object* v___x_3714_; 
v_fst_3712_ = lean_ctor_get(v_a_3708_, 0);
lean_inc(v_fst_3712_);
lean_dec(v_a_3708_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set_tag(v___x_3705_, 1);
lean_ctor_set(v___x_3705_, 0, v_fst_3712_);
v___x_3714_ = v___x_3705_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_fst_3712_);
v___x_3714_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3716_; 
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3714_);
v___x_3716_ = v___x_3710_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3714_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
else
{
lean_object* v_a_3720_; 
lean_del_object(v___x_3705_);
v_a_3720_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3720_);
lean_dec_ref(v___x_3707_);
v_a_3689_ = v_a_3720_;
goto v___jp_3688_;
}
}
}
else
{
lean_object* v_a_3722_; 
v_a_3722_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3722_);
lean_dec_ref(v___x_3702_);
v_a_3689_ = v_a_3722_;
goto v___jp_3688_;
}
}
}
}
}
}
else
{
lean_object* v___x_3727_; 
lean_del_object(v___x_3655_);
lean_dec(v_a_3653_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3420_);
lean_del_object(v___x_3417_);
lean_del_object(v___x_3408_);
lean_del_object(v___x_3401_);
lean_dec_ref(v_e_3370_);
v___x_3727_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3439_, v_a_3373_, v_a_3375_);
lean_dec(v_a_3439_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3735_; 
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v___x_3727_, 0);
lean_dec(v_unused_3736_);
v___x_3729_ = v___x_3727_;
v_isShared_3730_ = v_isSharedCheck_3735_;
goto v_resetjp_3728_;
}
else
{
lean_dec(v___x_3727_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3735_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3731_ = lean_box(0);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3731_);
v___x_3733_ = v___x_3729_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
v_a_3737_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3727_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3727_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3439_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3420_);
lean_del_object(v___x_3417_);
lean_del_object(v___x_3408_);
lean_del_object(v___x_3401_);
lean_dec_ref(v_e_3370_);
return v___x_3652_;
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_a_3439_);
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_del_object(v___x_3417_);
lean_del_object(v___x_3408_);
lean_dec(v_a_3406_);
lean_del_object(v___x_3401_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3747_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3440_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3440_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_del_object(v___x_3436_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
lean_del_object(v___x_3431_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_del_object(v___x_3417_);
lean_del_object(v___x_3408_);
lean_dec(v_a_3406_);
lean_del_object(v___x_3401_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3755_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3438_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3438_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
}
else
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
lean_dec(v_a_3425_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_del_object(v___x_3417_);
lean_del_object(v___x_3408_);
lean_dec(v_a_3406_);
lean_del_object(v___x_3401_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v___x_3765_ = lean_box(0);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 0, v___x_3765_);
v___x_3767_ = v___x_3427_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_del_object(v___x_3422_);
lean_dec(v_snd_3420_);
lean_dec(v_fst_3419_);
lean_del_object(v___x_3417_);
lean_del_object(v___x_3408_);
lean_dec(v_a_3406_);
lean_del_object(v___x_3401_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3770_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3424_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3424_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
}
else
{
lean_object* v___x_3780_; lean_object* v___x_3782_; 
lean_dec(v_a_3411_);
lean_del_object(v___x_3408_);
lean_dec(v_a_3406_);
lean_del_object(v___x_3401_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v___x_3780_ = lean_box(0);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3780_);
v___x_3782_ = v___x_3413_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_del_object(v___x_3408_);
lean_dec(v_a_3406_);
lean_del_object(v___x_3401_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3785_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3410_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3410_);
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
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_del_object(v___x_3401_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3370_);
v_a_3794_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3403_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3403_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3803_, lean_object* v_expectedType_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3803_, v_expectedType_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_);
lean_dec(v_a_3808_);
lean_dec_ref(v_a_3807_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3811_, lean_object* v_expectedType_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v___x_3818_; 
lean_inc_ref(v_expectedType_3812_);
lean_inc_ref(v_expr_3811_);
v___x_3818_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3811_, v_expectedType_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3898_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3821_ = v___x_3818_;
v_isShared_3822_ = v_isSharedCheck_3898_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3818_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3898_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
if (lean_obj_tag(v_a_3819_) == 1)
{
lean_object* v_val_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3835_; 
lean_dec_ref(v_expectedType_3812_);
lean_dec_ref(v_expr_3811_);
v_val_3823_ = lean_ctor_get(v_a_3819_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_a_3819_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3825_ = v_a_3819_;
v_isShared_3826_ = v_isSharedCheck_3835_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_val_3823_);
lean_dec(v_a_3819_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3835_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3830_; 
v___x_3827_ = lean_box(0);
v___x_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3828_, 0, v_val_3823_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3828_);
v___x_3830_ = v___x_3825_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3832_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v___x_3830_);
v___x_3832_ = v___x_3821_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
else
{
lean_object* v___x_3836_; 
lean_del_object(v___x_3821_);
lean_dec(v_a_3819_);
lean_inc_ref(v_expectedType_3812_);
v___x_3836_ = l_Lean_Meta_whnfR(v_expectedType_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; uint8_t v___x_3838_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref(v___x_3836_);
v___x_3838_ = l_Lean_Expr_isForall(v_a_3837_);
lean_dec(v_a_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3811_, v_expectedType_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
return v___x_3839_;
}
else
{
lean_object* v___x_3840_; 
lean_inc_ref(v_expr_3811_);
v___x_3840_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3811_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref(v___x_3840_);
if (lean_obj_tag(v_a_3841_) == 1)
{
lean_object* v_val_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3880_; 
v_val_3842_ = lean_ctor_get(v_a_3841_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v_a_3841_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3844_ = v_a_3841_;
v_isShared_3845_ = v_isSharedCheck_3880_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_val_3842_);
lean_dec(v_a_3841_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3880_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3846_; 
lean_inc(v_a_3816_);
lean_inc_ref(v_a_3815_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_val_3842_);
v___x_3846_ = lean_infer_type(v_val_3842_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3848_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref(v___x_3846_);
lean_inc_ref(v_expectedType_3812_);
v___x_3848_ = l_Lean_Meta_isExprDefEq(v_a_3847_, v_expectedType_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3863_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3851_ = v___x_3848_;
v_isShared_3852_ = v_isSharedCheck_3863_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3848_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3863_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
uint8_t v___x_3853_; 
v___x_3853_ = lean_unbox(v_a_3849_);
lean_dec(v_a_3849_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; 
lean_del_object(v___x_3851_);
lean_del_object(v___x_3844_);
lean_dec(v_val_3842_);
v___x_3854_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3811_, v_expectedType_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
return v___x_3854_;
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3858_; 
lean_dec_ref(v_expectedType_3812_);
lean_dec_ref(v_expr_3811_);
v___x_3855_ = lean_box(0);
v___x_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3856_, 0, v_val_3842_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 0, v___x_3856_);
v___x_3858_ = v___x_3844_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3860_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 0, v___x_3858_);
v___x_3860_ = v___x_3851_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3858_);
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
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_del_object(v___x_3844_);
lean_dec(v_val_3842_);
lean_dec_ref(v_expectedType_3812_);
lean_dec_ref(v_expr_3811_);
v_a_3864_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3848_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3848_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
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
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_del_object(v___x_3844_);
lean_dec(v_val_3842_);
lean_dec_ref(v_expectedType_3812_);
lean_dec_ref(v_expr_3811_);
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
else
{
lean_object* v___x_3881_; 
lean_dec(v_a_3841_);
v___x_3881_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3811_, v_expectedType_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
return v___x_3881_;
}
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
lean_dec_ref(v_expectedType_3812_);
lean_dec_ref(v_expr_3811_);
v_a_3882_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3840_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3840_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec_ref(v_expectedType_3812_);
lean_dec_ref(v_expr_3811_);
v_a_3890_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3836_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3836_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec_ref(v_expectedType_3812_);
lean_dec_ref(v_expr_3811_);
v_a_3899_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3818_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3818_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3907_, lean_object* v_expectedType_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3907_, v_expectedType_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3915_, lean_object* v_expectedType_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3915_, v_expectedType_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3947_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3925_ = v___x_3922_;
v_isShared_3926_ = v_isSharedCheck_3947_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3922_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3947_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
switch(lean_obj_tag(v_a_3923_))
{
case 0:
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = lean_box(0);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3927_);
v___x_3929_ = v___x_3925_;
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
case 1:
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3942_; 
v_a_3931_ = lean_ctor_get(v_a_3923_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_a_3923_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3933_ = v_a_3923_;
v_isShared_3934_ = v_isSharedCheck_3942_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v_a_3923_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3942_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v_fst_3935_; lean_object* v___x_3937_; 
v_fst_3935_ = lean_ctor_get(v_a_3931_, 0);
lean_inc(v_fst_3935_);
lean_dec(v_a_3931_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v_fst_3935_);
v___x_3937_ = v___x_3933_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_fst_3935_);
v___x_3937_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3939_; 
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3937_);
v___x_3939_ = v___x_3925_;
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
default: 
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3943_ = lean_box(2);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3943_);
v___x_3945_ = v___x_3925_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
v_a_3948_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3922_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3922_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3956_, lean_object* v_expectedType_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_Lean_Meta_coerce_x3f(v_expr_3956_, v_expectedType_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
return v_res_3963_;
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
