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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
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
lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; 
v___f_25_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_26_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_27_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_28_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_29_ = 0;
v___x_30_ = lean_box(2);
v___x_31_ = 0;
v___x_32_ = l_Lean_registerTagAttribute(v___x_26_, v___x_27_, v___f_25_, v___x_28_, v___x_29_, v___x_30_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1(){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_38_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0));
v___x_39_ = l_Lean_addBuiltinDocString(v___x_37_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___boxed(lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3(){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6));
v___x_70_ = l_Lean_addBuiltinDeclarationRanges(v___x_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
return v_res_72_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object* v_env_73_, lean_object* v_declName_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = l_Lean_Meta_coeDeclAttr;
v___x_76_ = l_Lean_TagAttribute_hasTag(v___x_75_, v_env_73_, v_declName_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object* v_env_77_, lean_object* v_declName_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_Meta_isCoeDecl(v_env_77_, v_declName_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(lean_object* v_declName_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; lean_object* v_env_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_84_ = lean_st_ref_get(v___y_82_);
v_env_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc_ref(v_env_85_);
lean_dec(v___x_84_);
v___x_86_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_85_, v_declName_81_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg___boxed(lean_object* v_declName_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_declName_88_, v___y_89_);
lean_dec(v___y_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0(lean_object* v_declName_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_declName_92_, v___y_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___boxed(lean_object* v_declName_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0(v_declName_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_box(0);
v___x_107_ = l_Lean_Expr_sort___override(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(lean_object* v_e_108_, lean_object* v_nm_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; 
lean_inc(v_nm_109_);
v___x_115_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_nm_109_, v_a_113_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_138_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_138_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_138_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_138_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
if (lean_obj_tag(v_a_116_) == 1)
{
lean_object* v_val_120_; lean_object* v_numParams_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v_val_120_ = lean_ctor_get(v_a_116_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v_a_116_, 1);
v_numParams_121_ = lean_ctor_get(v_val_120_, 1);
lean_inc(v_numParams_121_);
lean_dec(v_val_120_);
v___x_122_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v___x_123_ = l_Lean_Expr_getAppNumArgs(v_e_108_);
v___x_124_ = lean_nat_sub(v___x_123_, v_numParams_121_);
lean_dec(v_numParams_121_);
lean_dec(v___x_123_);
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_sub(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
v___x_127_ = l_Lean_Expr_getRevArgD(v_e_108_, v___x_126_, v___x_122_);
lean_dec_ref(v_e_108_);
v___x_128_ = l_Lean_Expr_getAppFn(v___x_127_);
v___x_129_ = l_Lean_Expr_isConst(v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_131_; 
lean_dec_ref(v___x_128_);
lean_dec_ref(v___x_127_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v_nm_109_);
v___x_131_ = v___x_118_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_nm_109_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
else
{
lean_object* v___x_133_; 
lean_del_object(v___x_118_);
lean_dec(v_nm_109_);
v___x_133_ = l_Lean_Expr_constName_x21(v___x_128_);
lean_dec_ref(v___x_128_);
v_e_108_ = v___x_127_;
v_nm_109_ = v___x_133_;
goto _start;
}
}
else
{
lean_object* v___x_136_; 
lean_dec(v_a_116_);
lean_dec_ref(v_e_108_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v_nm_109_);
v___x_136_ = v___x_118_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_nm_109_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_nm_109_);
lean_dec_ref(v_e_108_);
v_a_139_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_115_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_115_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___boxed(lean_object* v_e_147_, lean_object* v_nm_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_147_, v_nm_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__0(lean_object* v_e_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v_e_155_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___y_156_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__0___boxed(lean_object* v_e_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Meta_expandCoe___lam__0(v_e_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___lam__0(lean_object* v___x_173_, lean_object* v_entry_174_, lean_object* v_s_175_){
_start:
{
lean_object* v_addEntryFn_176_; lean_object* v_importedEntries_177_; lean_object* v_state_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_186_; 
v_addEntryFn_176_ = lean_ctor_get(v___x_173_, 3);
lean_inc(v_addEntryFn_176_);
lean_dec_ref(v___x_173_);
v_importedEntries_177_ = lean_ctor_get(v_s_175_, 0);
v_state_178_ = lean_ctor_get(v_s_175_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v_s_175_);
if (v_isSharedCheck_186_ == 0)
{
v___x_180_ = v_s_175_;
v_isShared_181_ = v_isSharedCheck_186_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_state_178_);
lean_inc(v_importedEntries_177_);
lean_dec(v_s_175_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_186_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_state_182_; lean_object* v___x_184_; 
v_state_182_ = lean_apply_2(v_addEntryFn_176_, v_state_178_, v_entry_174_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v_state_182_);
v___x_184_ = v___x_180_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_importedEntries_177_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_state_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(lean_object* v_msgData_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; lean_object* v_env_194_; uint8_t v___x_195_; lean_object* v_env_196_; lean_object* v___x_197_; lean_object* v_toCold_198_; lean_object* v_mctx_199_; lean_object* v_lctx_200_; lean_object* v_options_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_193_ = lean_st_ref_get(v___y_191_);
v_env_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc_ref(v_env_194_);
lean_dec(v___x_193_);
v___x_195_ = 0;
v_env_196_ = l_Lean_Environment_setRecordingDeps(v_env_194_, v___x_195_);
v___x_197_ = lean_st_ref_get(v___y_189_);
v_toCold_198_ = lean_ctor_get(v___y_190_, 0);
v_mctx_199_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref(v_mctx_199_);
lean_dec(v___x_197_);
v_lctx_200_ = lean_ctor_get(v___y_188_, 2);
v_options_201_ = lean_ctor_get(v_toCold_198_, 2);
lean_inc_ref(v_options_201_);
lean_inc_ref(v_lctx_200_);
v___x_202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_202_, 0, v_env_196_);
lean_ctor_set(v___x_202_, 1, v_mctx_199_);
lean_ctor_set(v___x_202_, 2, v_lctx_200_);
lean_ctor_set(v___x_202_, 3, v_options_201_);
v___x_203_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_msgData_187_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_msgData_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msgData_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_211_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_212_; double v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_float_of_nat(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object* v_cls_217_, lean_object* v_msg_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_ref_225_; lean_object* v___x_226_; lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_273_; 
v_ref_225_ = lean_ctor_get(v___y_222_, 2);
v___x_226_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_218_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_273_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_273_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_273_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v_traceState_232_; lean_object* v_env_233_; lean_object* v_nextMacroScope_234_; lean_object* v_ngen_235_; lean_object* v_auxDeclNGen_236_; lean_object* v_cache_237_; lean_object* v_recordedDeps_238_; lean_object* v_messages_239_; lean_object* v_infoState_240_; lean_object* v_snapshotTasks_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_272_; 
v___x_231_ = lean_st_ref_take(v___y_223_);
v_traceState_232_ = lean_ctor_get(v___x_231_, 4);
v_env_233_ = lean_ctor_get(v___x_231_, 0);
v_nextMacroScope_234_ = lean_ctor_get(v___x_231_, 1);
v_ngen_235_ = lean_ctor_get(v___x_231_, 2);
v_auxDeclNGen_236_ = lean_ctor_get(v___x_231_, 3);
v_cache_237_ = lean_ctor_get(v___x_231_, 5);
v_recordedDeps_238_ = lean_ctor_get(v___x_231_, 6);
v_messages_239_ = lean_ctor_get(v___x_231_, 7);
v_infoState_240_ = lean_ctor_get(v___x_231_, 8);
v_snapshotTasks_241_ = lean_ctor_get(v___x_231_, 9);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_272_ == 0)
{
v___x_243_ = v___x_231_;
v_isShared_244_ = v_isSharedCheck_272_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_snapshotTasks_241_);
lean_inc(v_infoState_240_);
lean_inc(v_messages_239_);
lean_inc(v_recordedDeps_238_);
lean_inc(v_cache_237_);
lean_inc(v_traceState_232_);
lean_inc(v_auxDeclNGen_236_);
lean_inc(v_ngen_235_);
lean_inc(v_nextMacroScope_234_);
lean_inc(v_env_233_);
lean_dec(v___x_231_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_272_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
uint64_t v_tid_245_; lean_object* v_traces_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_271_; 
v_tid_245_ = lean_ctor_get_uint64(v_traceState_232_, sizeof(void*)*1);
v_traces_246_ = lean_ctor_get(v_traceState_232_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v_traceState_232_);
if (v_isSharedCheck_271_ == 0)
{
v___x_248_ = v_traceState_232_;
v_isShared_249_ = v_isSharedCheck_271_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_traces_246_);
lean_dec(v_traceState_232_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_271_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; double v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_250_ = lean_box(0);
v___x_251_ = lean_box(0);
v___x_252_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0);
v___x_253_ = 0;
v___x_254_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_255_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_255_, 0, v_cls_217_);
lean_ctor_set(v___x_255_, 1, v___x_251_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
lean_ctor_set_float(v___x_255_, sizeof(void*)*3, v___x_252_);
lean_ctor_set_float(v___x_255_, sizeof(void*)*3 + 8, v___x_252_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*3 + 16, v___x_253_);
v___x_256_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2));
v___x_257_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v_a_227_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
lean_inc(v_ref_225_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_ref_225_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = l_Lean_PersistentArray_push___redArg(v_traces_246_, v___x_258_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_259_);
v___x_261_ = v___x_248_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_259_);
lean_ctor_set_uint64(v_reuseFailAlloc_270_, sizeof(void*)*1, v_tid_245_);
v___x_261_ = v_reuseFailAlloc_270_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 4, v___x_261_);
v___x_263_ = v___x_243_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_env_233_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_nextMacroScope_234_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_ngen_235_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_auxDeclNGen_236_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v_cache_237_);
lean_ctor_set(v_reuseFailAlloc_269_, 6, v_recordedDeps_238_);
lean_ctor_set(v_reuseFailAlloc_269_, 7, v_messages_239_);
lean_ctor_set(v_reuseFailAlloc_269_, 8, v_infoState_240_);
lean_ctor_set(v_reuseFailAlloc_269_, 9, v_snapshotTasks_241_);
v___x_263_ = v_reuseFailAlloc_269_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_264_ = lean_st_ref_put(v___y_223_, v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_250_);
lean_ctor_set(v___x_265_, 1, v___y_219_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_265_);
v___x_267_ = v___x_229_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_274_, lean_object* v_msg_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_274_, v_msg_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
return v_res_282_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_keys_283_, lean_object* v_i_284_, lean_object* v_k_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_array_get_size(v_keys_283_);
v___x_287_ = lean_nat_dec_lt(v_i_284_, v___x_286_);
if (v___x_287_ == 0)
{
lean_dec(v_i_284_);
return v___x_287_;
}
else
{
lean_object* v_k_x27_288_; uint8_t v___x_289_; 
v_k_x27_288_ = lean_array_fget_borrowed(v_keys_283_, v_i_284_);
v___x_289_ = l_Lean_instBEqExtraModUse_beq(v_k_285_, v_k_x27_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_add(v_i_284_, v___x_290_);
lean_dec(v_i_284_);
v_i_284_ = v___x_291_;
goto _start;
}
else
{
lean_dec(v_i_284_);
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_keys_293_, lean_object* v_i_294_, lean_object* v_k_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_293_, v_i_294_, v_k_295_);
lean_dec_ref(v_k_295_);
lean_dec_ref(v_keys_293_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_298_, size_t v_x_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
lean_object* v_es_301_; lean_object* v___x_302_; size_t v___x_303_; size_t v___x_304_; lean_object* v_j_305_; lean_object* v___x_306_; 
v_es_301_ = lean_ctor_get(v_x_298_, 0);
v___x_302_ = lean_box(2);
v___x_303_ = ((size_t)31ULL);
v___x_304_ = lean_usize_land(v_x_299_, v___x_303_);
v_j_305_ = lean_usize_to_nat(v___x_304_);
v___x_306_ = lean_array_get_borrowed(v___x_302_, v_es_301_, v_j_305_);
lean_dec(v_j_305_);
switch(lean_obj_tag(v___x_306_))
{
case 0:
{
lean_object* v_key_307_; uint8_t v___x_308_; 
v_key_307_ = lean_ctor_get(v___x_306_, 0);
v___x_308_ = l_Lean_instBEqExtraModUse_beq(v_x_300_, v_key_307_);
return v___x_308_;
}
case 1:
{
lean_object* v_node_309_; size_t v___x_310_; size_t v___x_311_; 
v_node_309_ = lean_ctor_get(v___x_306_, 0);
v___x_310_ = ((size_t)5ULL);
v___x_311_ = lean_usize_shift_right(v_x_299_, v___x_310_);
v_x_298_ = v_node_309_;
v_x_299_ = v___x_311_;
goto _start;
}
default: 
{
uint8_t v___x_313_; 
v___x_313_ = 0;
return v___x_313_;
}
}
}
else
{
lean_object* v_ks_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_ks_314_ = lean_ctor_get(v_x_298_, 0);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_314_, v___x_315_, v_x_300_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
size_t v_x_36429__boxed_320_; uint8_t v_res_321_; lean_object* v_r_322_; 
v_x_36429__boxed_320_ = lean_unbox_usize(v_x_318_);
lean_dec(v_x_318_);
v_res_321_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_317_, v_x_36429__boxed_320_, v_x_319_);
lean_dec_ref(v_x_319_);
lean_dec_ref(v_x_317_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
uint64_t v___x_325_; size_t v___x_326_; uint8_t v___x_327_; 
v___x_325_ = l_Lean_instHashableExtraModUse_hash(v_x_324_);
v___x_326_ = lean_uint64_to_usize(v___x_325_);
v___x_327_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_323_, v___x_326_, v_x_324_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_328_, v_x_329_);
lean_dec_ref(v_x_329_);
lean_dec_ref(v_x_328_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_332_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1);
v___x_338_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
lean_ctor_set(v___x_338_, 3, v___x_337_);
lean_ctor_set(v___x_338_, 4, v___x_337_);
lean_ctor_set(v___x_338_, 5, v___x_337_);
lean_ctor_set(v___x_338_, 6, v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_339_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9));
v___x_348_ = l_Lean_stringToMessageData(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v_cls_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_cls_354_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6));
v___x_355_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13));
v___x_356_ = l_Lean_Name_append(v___x_355_, v_cls_354_);
return v___x_356_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_367_, uint8_t v_isMeta_368_, lean_object* v_hint_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_env_412_; uint8_t v_isExporting_413_; lean_object* v_entry_414_; lean_object* v___x_415_; lean_object* v_env_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_410_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_411_ = lean_st_ref_get(v___y_374_);
v_env_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_ref(v_env_412_);
lean_dec(v___x_411_);
v_isExporting_413_ = lean_ctor_get_uint8(v_env_412_, sizeof(void*)*13);
lean_dec_ref(v_env_412_);
lean_inc(v_mod_367_);
v_entry_414_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_414_, 0, v_mod_367_);
lean_ctor_set_uint8(v_entry_414_, sizeof(void*)*1, v_isExporting_413_);
lean_ctor_set_uint8(v_entry_414_, sizeof(void*)*1 + 1, v_isMeta_368_);
v___x_415_ = lean_st_ref_get(v___y_374_);
v_env_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_ref(v_env_416_);
lean_dec(v___x_415_);
v___x_417_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_418_ = lean_box(1);
v___x_419_ = lean_box(0);
v___x_420_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_410_, v___x_417_, v_env_416_, v___x_418_, v___x_419_);
v___x_421_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_420_, v_entry_414_);
lean_dec(v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v_toCold_422_; lean_object* v_options_423_; lean_object* v_inheritedTraceOptions_424_; uint8_t v_hasTrace_425_; lean_object* v___f_426_; uint8_t v___x_427_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; 
v_toCold_422_ = lean_ctor_get(v___y_373_, 0);
v_options_423_ = lean_ctor_get(v_toCold_422_, 2);
v_inheritedTraceOptions_424_ = lean_ctor_get(v_toCold_422_, 11);
v_hasTrace_425_ = lean_ctor_get_uint8(v_options_423_, sizeof(void*)*1);
v___f_426_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_426_, 0, v___x_417_);
lean_closure_set(v___f_426_, 1, v_entry_414_);
v___x_427_ = 1;
if (v_hasTrace_425_ == 0)
{
lean_dec(v_hint_369_);
lean_dec(v_mod_367_);
v___y_429_ = v___y_370_;
v___y_430_ = v___y_372_;
v___y_431_ = v___y_374_;
goto v___jp_428_;
}
else
{
lean_object* v_cls_458_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___x_480_; uint8_t v___x_481_; 
v_cls_458_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6));
v___x_480_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14);
v___x_481_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_424_, v_options_423_, v___x_480_);
if (v___x_481_ == 0)
{
lean_dec(v_hint_369_);
lean_dec(v_mod_367_);
v___y_429_ = v___y_370_;
v___y_430_ = v___y_372_;
v___y_431_ = v___y_374_;
goto v___jp_428_;
}
else
{
lean_object* v___x_482_; lean_object* v___y_484_; 
v___x_482_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
if (v_isExporting_413_ == 0)
{
lean_object* v___x_491_; 
v___x_491_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_484_ = v___x_491_;
goto v___jp_483_;
}
else
{
lean_object* v___x_492_; 
v___x_492_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
v___y_484_ = v___x_492_;
goto v___jp_483_;
}
v___jp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc_ref(v___y_484_);
v___x_485_ = l_Lean_stringToMessageData(v___y_484_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_482_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
if (v_isMeta_368_ == 0)
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___y_467_ = v___x_488_;
v___y_468_ = v___x_489_;
goto v___jp_466_;
}
else
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20));
v___y_467_ = v___x_488_;
v___y_468_ = v___x_490_;
goto v___jp_466_;
}
}
}
v___jp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_462_, 0, v___y_460_);
lean_ctor_set(v___x_462_, 1, v___y_461_);
v___x_463_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_458_, v___x_462_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v_snd_465_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v_snd_465_ = lean_ctor_get(v_a_464_, 1);
lean_inc(v_snd_465_);
lean_dec(v_a_464_);
v___y_429_ = v_snd_465_;
v___y_430_ = v___y_372_;
v___y_431_ = v___y_374_;
goto v___jp_428_;
}
else
{
lean_dec_ref(v___f_426_);
return v___x_463_;
}
}
v___jp_466_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
lean_inc_ref(v___y_468_);
v___x_469_ = l_Lean_stringToMessageData(v___y_468_);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___y_467_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Lean_MessageData_ofName(v_mod_367_);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = l_Lean_Name_isAnonymous(v_hint_369_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_477_ = l_Lean_MessageData_ofName(v_hint_369_);
v___x_478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___y_460_ = v___x_474_;
v___y_461_ = v___x_478_;
goto v___jp_459_;
}
else
{
lean_object* v___x_479_; 
lean_dec(v_hint_369_);
v___x_479_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11);
v___y_460_ = v___x_474_;
v___y_461_ = v___x_479_;
goto v___jp_459_;
}
}
}
v___jp_428_:
{
lean_object* v___x_432_; lean_object* v_toEnvExtension_433_; uint8_t v_logWrites_434_; 
v___x_432_ = lean_st_ref_take(v___y_431_);
v_toEnvExtension_433_ = lean_ctor_get(v___x_417_, 0);
v_logWrites_434_ = lean_ctor_get_uint8(v_toEnvExtension_433_, sizeof(void*)*6);
if (v_logWrites_434_ == 0)
{
lean_object* v_env_435_; lean_object* v_nextMacroScope_436_; lean_object* v_ngen_437_; lean_object* v_auxDeclNGen_438_; lean_object* v_traceState_439_; lean_object* v_recordedDeps_440_; lean_object* v_messages_441_; lean_object* v_infoState_442_; lean_object* v_snapshotTasks_443_; lean_object* v_asyncMode_444_; lean_object* v___x_445_; 
v_env_435_ = lean_ctor_get(v___x_432_, 0);
lean_inc_ref(v_env_435_);
v_nextMacroScope_436_ = lean_ctor_get(v___x_432_, 1);
lean_inc(v_nextMacroScope_436_);
v_ngen_437_ = lean_ctor_get(v___x_432_, 2);
lean_inc_ref(v_ngen_437_);
v_auxDeclNGen_438_ = lean_ctor_get(v___x_432_, 3);
lean_inc_ref(v_auxDeclNGen_438_);
v_traceState_439_ = lean_ctor_get(v___x_432_, 4);
lean_inc_ref(v_traceState_439_);
v_recordedDeps_440_ = lean_ctor_get(v___x_432_, 6);
lean_inc_ref(v_recordedDeps_440_);
v_messages_441_ = lean_ctor_get(v___x_432_, 7);
lean_inc_ref(v_messages_441_);
v_infoState_442_ = lean_ctor_get(v___x_432_, 8);
lean_inc_ref(v_infoState_442_);
v_snapshotTasks_443_ = lean_ctor_get(v___x_432_, 9);
lean_inc_ref(v_snapshotTasks_443_);
lean_dec(v___x_432_);
v_asyncMode_444_ = lean_ctor_get(v_toEnvExtension_433_, 2);
lean_inc_ref(v_toEnvExtension_433_);
v___x_445_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_433_, v_env_435_, v___f_426_, v_asyncMode_444_, v___x_419_, v___x_427_);
v___y_377_ = v_snapshotTasks_443_;
v___y_378_ = v_traceState_439_;
v___y_379_ = v_auxDeclNGen_438_;
v___y_380_ = v_ngen_437_;
v___y_381_ = v_nextMacroScope_436_;
v___y_382_ = v_infoState_442_;
v___y_383_ = v___y_429_;
v___y_384_ = v_messages_441_;
v___y_385_ = v___y_430_;
v___y_386_ = v___y_431_;
v___y_387_ = v_recordedDeps_440_;
v___y_388_ = v___x_445_;
goto v___jp_376_;
}
else
{
lean_object* v_env_446_; lean_object* v_nextMacroScope_447_; lean_object* v_ngen_448_; lean_object* v_auxDeclNGen_449_; lean_object* v_traceState_450_; lean_object* v_recordedDeps_451_; lean_object* v_messages_452_; lean_object* v_infoState_453_; lean_object* v_snapshotTasks_454_; lean_object* v_asyncMode_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_env_446_ = lean_ctor_get(v___x_432_, 0);
lean_inc_ref(v_env_446_);
v_nextMacroScope_447_ = lean_ctor_get(v___x_432_, 1);
lean_inc(v_nextMacroScope_447_);
v_ngen_448_ = lean_ctor_get(v___x_432_, 2);
lean_inc_ref(v_ngen_448_);
v_auxDeclNGen_449_ = lean_ctor_get(v___x_432_, 3);
lean_inc_ref(v_auxDeclNGen_449_);
v_traceState_450_ = lean_ctor_get(v___x_432_, 4);
lean_inc_ref(v_traceState_450_);
v_recordedDeps_451_ = lean_ctor_get(v___x_432_, 6);
lean_inc_ref(v_recordedDeps_451_);
v_messages_452_ = lean_ctor_get(v___x_432_, 7);
lean_inc_ref(v_messages_452_);
v_infoState_453_ = lean_ctor_get(v___x_432_, 8);
lean_inc_ref(v_infoState_453_);
v_snapshotTasks_454_ = lean_ctor_get(v___x_432_, 9);
lean_inc_ref(v_snapshotTasks_454_);
lean_dec(v___x_432_);
v_asyncMode_455_ = lean_ctor_get(v_toEnvExtension_433_, 2);
lean_inc_ref_n(v_toEnvExtension_433_, 2);
v___x_456_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_433_, v_env_446_);
lean_dec_ref(v_env_446_);
v___x_457_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_433_, v___x_456_, v___f_426_, v_asyncMode_455_, v___x_419_, v___x_427_);
v___y_377_ = v_snapshotTasks_454_;
v___y_378_ = v_traceState_450_;
v___y_379_ = v_auxDeclNGen_449_;
v___y_380_ = v_ngen_448_;
v___y_381_ = v_nextMacroScope_447_;
v___y_382_ = v_infoState_453_;
v___y_383_ = v___y_429_;
v___y_384_ = v_messages_452_;
v___y_385_ = v___y_430_;
v___y_386_ = v___y_431_;
v___y_387_ = v_recordedDeps_451_;
v___y_388_ = v___x_457_;
goto v___jp_376_;
}
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec_ref_known(v_entry_414_, 1);
lean_dec(v_hint_369_);
lean_dec(v_mod_367_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___y_370_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
v___jp_376_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_mctx_393_; lean_object* v_zetaDeltaFVarIds_394_; lean_object* v_postponed_395_; lean_object* v_diag_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_408_; 
v___x_389_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
v___x_390_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_390_, 0, v___y_388_);
lean_ctor_set(v___x_390_, 1, v___y_381_);
lean_ctor_set(v___x_390_, 2, v___y_380_);
lean_ctor_set(v___x_390_, 3, v___y_379_);
lean_ctor_set(v___x_390_, 4, v___y_378_);
lean_ctor_set(v___x_390_, 5, v___x_389_);
lean_ctor_set(v___x_390_, 6, v___y_387_);
lean_ctor_set(v___x_390_, 7, v___y_384_);
lean_ctor_set(v___x_390_, 8, v___y_382_);
lean_ctor_set(v___x_390_, 9, v___y_377_);
v___x_391_ = lean_st_ref_put(v___y_386_, v___x_390_);
v___x_392_ = lean_st_ref_take(v___y_385_);
v_mctx_393_ = lean_ctor_get(v___x_392_, 0);
v_zetaDeltaFVarIds_394_ = lean_ctor_get(v___x_392_, 2);
v_postponed_395_ = lean_ctor_get(v___x_392_, 3);
v_diag_396_ = lean_ctor_get(v___x_392_, 4);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_392_, 1);
lean_dec(v_unused_409_);
v___x_398_ = v___x_392_;
v_isShared_399_ = v_isSharedCheck_408_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_diag_396_);
lean_inc(v_postponed_395_);
lean_inc(v_zetaDeltaFVarIds_394_);
lean_inc(v_mctx_393_);
lean_dec(v___x_392_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_408_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_400_ = lean_box(0);
v___x_401_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v___x_401_);
v___x_403_ = v___x_398_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_mctx_393_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_zetaDeltaFVarIds_394_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_postponed_395_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_diag_396_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_st_ref_put(v___y_385_, v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_400_);
lean_ctor_set(v___x_405_, 1, v___y_383_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object* v_mod_496_, lean_object* v_isMeta_497_, lean_object* v_hint_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
uint8_t v_isMeta_boxed_505_; lean_object* v_res_506_; 
v_isMeta_boxed_505_ = lean_unbox(v_isMeta_497_);
v_res_506_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_496_, v_isMeta_boxed_505_, v_hint_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object* v_a_507_, lean_object* v_x_508_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v___x_509_; 
v___x_509_ = lean_box(0);
return v___x_509_;
}
else
{
lean_object* v_key_510_; lean_object* v_value_511_; lean_object* v_tail_512_; uint8_t v___x_513_; 
v_key_510_ = lean_ctor_get(v_x_508_, 0);
v_value_511_ = lean_ctor_get(v_x_508_, 1);
v_tail_512_ = lean_ctor_get(v_x_508_, 2);
v___x_513_ = lean_name_eq(v_key_510_, v_a_507_);
if (v___x_513_ == 0)
{
v_x_508_ = v_tail_512_;
goto _start;
}
else
{
lean_object* v___x_515_; 
lean_inc(v_value_511_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v_value_511_);
return v___x_515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_516_, lean_object* v_x_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_516_, v_x_517_);
lean_dec(v_x_517_);
lean_dec(v_a_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_buckets_521_; lean_object* v___x_522_; uint64_t v___y_524_; 
v_buckets_521_ = lean_ctor_get(v_m_519_, 1);
v___x_522_ = lean_array_get_size(v_buckets_521_);
if (lean_obj_tag(v_a_520_) == 0)
{
uint64_t v___x_538_; 
v___x_538_ = 1723ULL;
v___y_524_ = v___x_538_;
goto v___jp_523_;
}
else
{
uint64_t v_hash_539_; 
v_hash_539_ = lean_ctor_get_uint64(v_a_520_, sizeof(void*)*2);
v___y_524_ = v_hash_539_;
goto v___jp_523_;
}
v___jp_523_:
{
uint64_t v___x_525_; uint64_t v___x_526_; uint64_t v_fold_527_; uint64_t v___x_528_; uint64_t v___x_529_; uint64_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; size_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_525_ = 32ULL;
v___x_526_ = lean_uint64_shift_right(v___y_524_, v___x_525_);
v_fold_527_ = lean_uint64_xor(v___y_524_, v___x_526_);
v___x_528_ = 16ULL;
v___x_529_ = lean_uint64_shift_right(v_fold_527_, v___x_528_);
v___x_530_ = lean_uint64_xor(v_fold_527_, v___x_529_);
v___x_531_ = lean_uint64_to_usize(v___x_530_);
v___x_532_ = lean_usize_of_nat(v___x_522_);
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_sub(v___x_532_, v___x_533_);
v___x_535_ = lean_usize_land(v___x_531_, v___x_534_);
v___x_536_ = lean_array_uget_borrowed(v_buckets_521_, v___x_535_);
v___x_537_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_520_, v___x_536_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_m_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_543_, lean_object* v_declName_544_, lean_object* v_as_545_, size_t v_sz_546_, size_t v_i_547_, lean_object* v_b_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = lean_usize_dec_lt(v_i_547_, v_sz_546_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v_declName_544_);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v_b_548_);
lean_ctor_set(v___x_556_, 1, v___y_549_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; lean_object* v_modules_559_; lean_object* v___x_560_; lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v_toImport_563_; lean_object* v_module_564_; lean_object* v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; 
v___x_558_ = l_Lean_Environment_header(v___x_543_);
v_modules_559_ = lean_ctor_get(v___x_558_, 3);
lean_inc_ref(v_modules_559_);
lean_dec_ref(v___x_558_);
v___x_560_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_561_ = lean_array_uget_borrowed(v_as_545_, v_i_547_);
v___x_562_ = lean_array_get(v___x_560_, v_modules_559_, v_a_561_);
lean_dec_ref(v_modules_559_);
v_toImport_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_toImport_563_);
lean_dec(v___x_562_);
v_module_564_ = lean_ctor_get(v_toImport_563_, 0);
lean_inc(v_module_564_);
lean_dec_ref(v_toImport_563_);
v___x_565_ = lean_box(0);
v___x_566_ = 0;
lean_inc(v_declName_544_);
v___x_567_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_564_, v___x_566_, v_declName_544_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v_snd_569_; size_t v___x_570_; size_t v___x_571_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
v_snd_569_ = lean_ctor_get(v_a_568_, 1);
lean_inc(v_snd_569_);
lean_dec(v_a_568_);
v___x_570_ = ((size_t)1ULL);
v___x_571_ = lean_usize_add(v_i_547_, v___x_570_);
v_i_547_ = v___x_571_;
v_b_548_ = v___x_565_;
v___y_549_ = v_snd_569_;
goto _start;
}
else
{
lean_dec(v_declName_544_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_573_, lean_object* v_declName_574_, lean_object* v_as_575_, lean_object* v_sz_576_, lean_object* v_i_577_, lean_object* v_b_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
size_t v_sz_boxed_585_; size_t v_i_boxed_586_; lean_object* v_res_587_; 
v_sz_boxed_585_ = lean_unbox_usize(v_sz_576_);
lean_dec(v_sz_576_);
v_i_boxed_586_ = lean_unbox_usize(v_i_577_);
lean_dec(v_i_577_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_573_, v_declName_574_, v_as_575_, v_sz_boxed_585_, v_i_boxed_586_, v_b_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v_as_575_);
lean_dec_ref(v___x_573_);
return v_res_587_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0(void){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_HashMap_instInhabited___redArg();
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_591_, uint8_t v_isMeta_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_env_605_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___x_630_; 
v___x_599_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0);
v___x_600_ = lean_st_ref_get(v___y_597_);
v_env_605_ = lean_ctor_get(v___x_600_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_600_);
v___x_630_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_605_, v_declName_591_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_dec_ref(v_env_605_);
lean_dec(v_declName_591_);
goto v___jp_601_;
}
else
{
lean_object* v_val_631_; lean_object* v___x_632_; lean_object* v_modules_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = l_Lean_Environment_header(v_env_605_);
v_modules_633_ = lean_ctor_get(v___x_632_, 3);
lean_inc_ref(v_modules_633_);
lean_dec_ref(v___x_632_);
v___x_634_ = lean_array_get_size(v_modules_633_);
v___x_635_ = lean_nat_dec_lt(v_val_631_, v___x_634_);
if (v___x_635_ == 0)
{
lean_dec_ref(v_modules_633_);
lean_dec(v_val_631_);
lean_dec_ref(v_env_605_);
lean_dec(v_declName_591_);
goto v___jp_601_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___y_639_; 
v___x_636_ = lean_array_fget(v_modules_633_, v_val_631_);
lean_dec(v_val_631_);
lean_dec_ref(v_modules_633_);
v___x_637_ = lean_st_ref_get(v___y_597_);
if (v_isMeta_592_ == 0)
{
lean_dec(v___x_637_);
v___y_639_ = v_isMeta_592_;
goto v___jp_638_;
}
else
{
lean_object* v_env_652_; uint8_t v___x_653_; 
v_env_652_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_env_652_);
lean_dec(v___x_637_);
lean_inc(v_declName_591_);
v___x_653_ = l_Lean_isMarkedMeta(v_env_652_, v_declName_591_);
if (v___x_653_ == 0)
{
v___y_639_ = v_isMeta_592_;
goto v___jp_638_;
}
else
{
uint8_t v___x_654_; 
v___x_654_ = 0;
v___y_639_ = v___x_654_;
goto v___jp_638_;
}
}
v___jp_638_:
{
lean_object* v_toImport_640_; lean_object* v_module_641_; lean_object* v___x_642_; 
v_toImport_640_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_toImport_640_);
lean_dec(v___x_636_);
v_module_641_ = lean_ctor_get(v_toImport_640_, 0);
lean_inc(v_module_641_);
lean_dec_ref(v_toImport_640_);
lean_inc(v_declName_591_);
v___x_642_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_641_, v___y_639_, v_declName_591_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v_snd_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v_snd_644_ = lean_ctor_get(v_a_643_, 1);
lean_inc(v_snd_644_);
lean_dec(v_a_643_);
v___x_645_ = l_Lean_indirectModUseExt;
v___x_646_ = lean_box(1);
v___x_647_ = lean_box(0);
lean_inc_ref(v_env_605_);
v___x_648_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_599_, v___x_645_, v_env_605_, v___x_646_, v___x_647_);
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_648_, v_declName_591_);
lean_dec(v___x_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_650_; 
v___x_650_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___y_607_ = v_snd_644_;
v___y_608_ = v___x_650_;
goto v___jp_606_;
}
else
{
lean_object* v_val_651_; 
v_val_651_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v___x_649_, 1);
v___y_607_ = v_snd_644_;
v___y_608_ = v_val_651_;
goto v___jp_606_;
}
}
else
{
lean_dec_ref(v_env_605_);
lean_dec(v_declName_591_);
return v___x_642_;
}
}
}
}
v___jp_601_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_box(0);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___y_593_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
v___jp_606_:
{
lean_object* v___x_609_; size_t v_sz_610_; size_t v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_box(0);
v_sz_610_ = lean_array_size(v___y_608_);
v___x_611_ = ((size_t)0ULL);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_605_, v_declName_591_, v___y_608_, v_sz_610_, v___x_611_, v___x_609_, v___y_607_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec_ref(v___y_608_);
lean_dec_ref(v_env_605_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_629_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_629_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_629_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_629_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_snd_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_627_; 
v_snd_617_ = lean_ctor_get(v_a_613_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_a_613_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v_a_613_, 0);
lean_dec(v_unused_628_);
v___x_619_ = v_a_613_;
v_isShared_620_ = v_isSharedCheck_627_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_snd_617_);
lean_dec(v_a_613_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_627_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_609_);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_snd_617_);
v___x_622_ = v_reuseFailAlloc_626_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_622_);
v___x_624_ = v___x_615_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
else
{
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_655_, lean_object* v_isMeta_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v_isMeta_boxed_663_; lean_object* v_res_664_; 
v_isMeta_boxed_663_ = lean_unbox(v_isMeta_656_);
v_res_664_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_655_, v_isMeta_boxed_663_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___y_680_; lean_object* v_f_684_; uint8_t v___x_685_; 
v_f_684_ = l_Lean_Expr_getAppFn(v_e_672_);
v___x_685_ = l_Lean_Expr_isConst(v_f_684_);
if (v___x_685_ == 0)
{
lean_dec_ref(v_f_684_);
lean_dec_ref(v_e_672_);
v___y_680_ = v___y_673_;
goto v___jp_679_;
}
else
{
lean_object* v_declName_686_; lean_object* v___x_687_; lean_object* v_env_688_; uint8_t v___x_689_; 
v_declName_686_ = l_Lean_Expr_constName_x21(v_f_684_);
lean_dec_ref(v_f_684_);
v___x_687_ = lean_st_ref_get(v___y_677_);
v_env_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc_ref(v_env_688_);
lean_dec(v___x_687_);
lean_inc(v_declName_686_);
v___x_689_ = l_Lean_Meta_isCoeDecl(v_env_688_, v_declName_686_);
if (v___x_689_ == 0)
{
lean_dec(v_declName_686_);
lean_dec_ref(v_e_672_);
v___y_680_ = v___y_673_;
goto v___jp_679_;
}
else
{
lean_object* v___x_690_; 
lean_inc(v_declName_686_);
lean_inc_ref(v_e_672_);
v___x_690_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_672_, v_declName_686_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; uint8_t v___x_692_; lean_object* v___x_693_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = 0;
v___x_693_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_691_, v___x_692_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v_snd_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_746_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v_snd_695_ = lean_ctor_get(v_a_694_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_a_694_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v_a_694_, 0);
lean_dec(v_unused_747_);
v___x_697_ = v_a_694_;
v_isShared_698_ = v_isSharedCheck_746_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snd_695_);
lean_dec(v_a_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_746_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; 
lean_inc_ref(v_e_672_);
v___x_699_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_672_, v___x_692_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_737_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_737_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_737_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_737_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
if (lean_obj_tag(v_a_700_) == 1)
{
lean_object* v_val_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_736_; 
v_val_704_ = lean_ctor_get(v_a_700_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_a_700_);
if (v_isSharedCheck_736_ == 0)
{
v___x_706_ = v_a_700_;
v_isShared_707_ = v_isSharedCheck_736_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_val_704_);
lean_dec(v_a_700_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_736_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___y_709_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_721_ = lean_name_eq(v_declName_686_, v___x_720_);
lean_dec(v_declName_686_);
if (v___x_721_ == 0)
{
lean_dec_ref(v_e_672_);
v___y_709_ = v_snd_695_;
goto v___jp_708_;
}
else
{
lean_object* v_dummy_722_; lean_object* v_nargs_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_dummy_722_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_723_ = l_Lean_Expr_getAppNumArgs(v_e_672_);
lean_inc(v_nargs_723_);
v___x_724_ = lean_mk_array(v_nargs_723_, v_dummy_722_);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_sub(v_nargs_723_, v___x_725_);
lean_dec(v_nargs_723_);
v___x_727_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_672_, v___x_724_, v___x_726_);
v___x_728_ = lean_unsigned_to_nat(2u);
v___x_729_ = lean_array_get_size(v___x_727_);
v___x_730_ = lean_nat_dec_lt(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_dec_ref(v___x_727_);
v___y_709_ = v_snd_695_;
goto v___jp_708_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = lean_array_fget(v___x_727_, v___x_728_);
lean_dec_ref(v___x_727_);
v___x_732_ = l_Lean_Expr_getAppFn(v___x_731_);
lean_dec(v___x_731_);
v___x_733_ = l_Lean_Expr_isConst(v___x_732_);
if (v___x_733_ == 0)
{
lean_dec_ref(v___x_732_);
v___y_709_ = v_snd_695_;
goto v___jp_708_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = l_Lean_Expr_constName_x21(v___x_732_);
lean_dec_ref(v___x_732_);
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v_snd_695_);
v___y_709_ = v___x_735_;
goto v___jp_708_;
}
}
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = l_Lean_Expr_headBeta(v_val_704_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_710_);
v___x_712_ = v___x_706_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_719_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___y_709_);
lean_ctor_set(v___x_697_, 0, v___x_712_);
v___x_714_ = v___x_697_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___y_709_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_714_);
v___x_716_ = v___x_702_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_702_);
lean_dec(v_a_700_);
lean_del_object(v___x_697_);
lean_dec(v_declName_686_);
lean_dec_ref(v_e_672_);
v___y_680_ = v_snd_695_;
goto v___jp_679_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_del_object(v___x_697_);
lean_dec(v_snd_695_);
lean_dec(v_declName_686_);
lean_dec_ref(v_e_672_);
v_a_738_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_699_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_699_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_declName_686_);
lean_dec_ref(v_e_672_);
v_a_748_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_693_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_693_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_declName_686_);
lean_dec(v___y_673_);
lean_dec_ref(v_e_672_);
v_a_756_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_690_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_690_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___y_680_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Meta_expandCoe___lam__1(v_e_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(lean_object* v_k_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; 
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
lean_inc(v___y_773_);
v___x_781_ = lean_apply_8(v_k_772_, v_b_775_, v___y_773_, v___y_774_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, lean_box(0));
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed(lean_object* v_k_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v_b_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(v_k_782_, v___y_783_, v___y_784_, v_b_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_783_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object* v_name_792_, uint8_t v_bi_793_, lean_object* v_type_794_, lean_object* v_k_795_, uint8_t v_kind_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___f_804_; lean_object* v___x_805_; 
lean_inc(v___y_797_);
v___f_804_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_804_, 0, v_k_795_);
lean_closure_set(v___f_804_, 1, v___y_797_);
lean_closure_set(v___f_804_, 2, v___y_798_);
v___x_805_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_792_, v_bi_793_, v_type_794_, v___f_804_, v_kind_796_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
v_a_814_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_805_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_805_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object* v_name_822_, lean_object* v_bi_823_, lean_object* v_type_824_, lean_object* v_k_825_, lean_object* v_kind_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
uint8_t v_bi_boxed_834_; uint8_t v_kind_boxed_835_; lean_object* v_res_836_; 
v_bi_boxed_834_ = lean_unbox(v_bi_823_);
v_kind_boxed_835_ = lean_unbox(v_kind_826_);
v_res_836_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_822_, v_bi_boxed_834_, v_type_824_, v_k_825_, v_kind_boxed_835_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_827_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object* v___x_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_837_);
lean_ctor_set(v___x_844_, 1, v___y_838_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(lean_object* v_name_854_, lean_object* v_type_855_, lean_object* v_val_856_, lean_object* v_k_857_, uint8_t v_nondep_858_, uint8_t v_kind_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___f_867_; lean_object* v___x_868_; 
lean_inc(v___y_860_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_867_, 0, v_k_857_);
lean_closure_set(v___f_867_, 1, v___y_860_);
lean_closure_set(v___f_867_, 2, v___y_861_);
v___x_868_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_854_, v_type_855_, v_val_856_, v___f_867_, v_nondep_858_, v_kind_859_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_868_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_868_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg___boxed(lean_object* v_name_885_, lean_object* v_type_886_, lean_object* v_val_887_, lean_object* v_k_888_, lean_object* v_nondep_889_, lean_object* v_kind_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
uint8_t v_nondep_boxed_898_; uint8_t v_kind_boxed_899_; lean_object* v_res_900_; 
v_nondep_boxed_898_ = lean_unbox(v_nondep_889_);
v_kind_boxed_899_ = lean_unbox(v_kind_890_);
v_res_900_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_885_, v_type_886_, v_val_887_, v_k_888_, v_nondep_boxed_898_, v_kind_boxed_899_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_891_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(lean_object* v_a_901_, lean_object* v_b_902_, lean_object* v_x_903_){
_start:
{
if (lean_obj_tag(v_x_903_) == 0)
{
lean_dec(v_b_902_);
lean_dec_ref(v_a_901_);
return v_x_903_;
}
else
{
lean_object* v_key_904_; lean_object* v_value_905_; lean_object* v_tail_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_918_; 
v_key_904_ = lean_ctor_get(v_x_903_, 0);
v_value_905_ = lean_ctor_get(v_x_903_, 1);
v_tail_906_ = lean_ctor_get(v_x_903_, 2);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_903_);
if (v_isSharedCheck_918_ == 0)
{
v___x_908_ = v_x_903_;
v_isShared_909_ = v_isSharedCheck_918_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_tail_906_);
lean_inc(v_value_905_);
lean_inc(v_key_904_);
lean_dec(v_x_903_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_918_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
uint8_t v___x_910_; 
v___x_910_ = l_Lean_ExprStructEq_beq(v_key_904_, v_a_901_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_901_, v_b_902_, v_tail_906_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 2, v___x_911_);
v___x_913_ = v___x_908_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_key_904_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_value_905_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
else
{
lean_object* v___x_916_; 
lean_dec(v_value_905_);
lean_dec(v_key_904_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v_b_902_);
lean_ctor_set(v___x_908_, 0, v_a_901_);
v___x_916_ = v___x_908_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_901_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_b_902_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_tail_906_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object* v_a_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
uint8_t v___x_921_; 
v___x_921_ = 0;
return v___x_921_;
}
else
{
lean_object* v_key_922_; lean_object* v_tail_923_; uint8_t v___x_924_; 
v_key_922_ = lean_ctor_get(v_x_920_, 0);
v_tail_923_ = lean_ctor_get(v_x_920_, 2);
v___x_924_ = l_Lean_ExprStructEq_beq(v_key_922_, v_a_919_);
if (v___x_924_ == 0)
{
v_x_920_ = v_tail_923_;
goto _start;
}
else
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object* v_a_926_, lean_object* v_x_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_926_, v_x_927_);
lean_dec(v_x_927_);
lean_dec_ref(v_a_926_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
if (lean_obj_tag(v_x_931_) == 0)
{
return v_x_930_;
}
else
{
lean_object* v_key_932_; lean_object* v_value_933_; lean_object* v_tail_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_957_; 
v_key_932_ = lean_ctor_get(v_x_931_, 0);
v_value_933_ = lean_ctor_get(v_x_931_, 1);
v_tail_934_ = lean_ctor_get(v_x_931_, 2);
v_isSharedCheck_957_ = !lean_is_exclusive(v_x_931_);
if (v_isSharedCheck_957_ == 0)
{
v___x_936_ = v_x_931_;
v_isShared_937_ = v_isSharedCheck_957_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_tail_934_);
lean_inc(v_value_933_);
lean_inc(v_key_932_);
lean_dec(v_x_931_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_957_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; uint64_t v___x_939_; uint64_t v___x_940_; uint64_t v___x_941_; uint64_t v_fold_942_; uint64_t v___x_943_; uint64_t v___x_944_; uint64_t v___x_945_; size_t v___x_946_; size_t v___x_947_; size_t v___x_948_; size_t v___x_949_; size_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_938_ = lean_array_get_size(v_x_930_);
v___x_939_ = l_Lean_ExprStructEq_hash(v_key_932_);
v___x_940_ = 32ULL;
v___x_941_ = lean_uint64_shift_right(v___x_939_, v___x_940_);
v_fold_942_ = lean_uint64_xor(v___x_939_, v___x_941_);
v___x_943_ = 16ULL;
v___x_944_ = lean_uint64_shift_right(v_fold_942_, v___x_943_);
v___x_945_ = lean_uint64_xor(v_fold_942_, v___x_944_);
v___x_946_ = lean_uint64_to_usize(v___x_945_);
v___x_947_ = lean_usize_of_nat(v___x_938_);
v___x_948_ = ((size_t)1ULL);
v___x_949_ = lean_usize_sub(v___x_947_, v___x_948_);
v___x_950_ = lean_usize_land(v___x_946_, v___x_949_);
v___x_951_ = lean_array_uget_borrowed(v_x_930_, v___x_950_);
lean_inc(v___x_951_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 2, v___x_951_);
v___x_953_ = v___x_936_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_key_932_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_value_933_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v___x_951_);
v___x_953_ = v_reuseFailAlloc_956_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; 
v___x_954_ = lean_array_uset(v_x_930_, v___x_950_, v___x_953_);
v_x_930_ = v___x_954_;
v_x_931_ = v_tail_934_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(lean_object* v_i_958_, lean_object* v_source_959_, lean_object* v_target_960_){
_start:
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = lean_array_get_size(v_source_959_);
v___x_962_ = lean_nat_dec_lt(v_i_958_, v___x_961_);
if (v___x_962_ == 0)
{
lean_dec_ref(v_source_959_);
lean_dec(v_i_958_);
return v_target_960_;
}
else
{
lean_object* v_es_963_; lean_object* v___x_964_; lean_object* v_source_965_; lean_object* v_target_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_es_963_ = lean_array_fget(v_source_959_, v_i_958_);
v___x_964_ = lean_box(0);
v_source_965_ = lean_array_fset(v_source_959_, v_i_958_, v___x_964_);
v_target_966_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_target_960_, v_es_963_);
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_add(v_i_958_, v___x_967_);
lean_dec(v_i_958_);
v_i_958_ = v___x_968_;
v_source_959_ = v_source_965_;
v_target_960_ = v_target_966_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object* v_data_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_nbuckets_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_971_ = lean_array_get_size(v_data_970_);
v___x_972_ = lean_unsigned_to_nat(2u);
v_nbuckets_973_ = lean_nat_mul(v___x_971_, v___x_972_);
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_box(0);
v___x_976_ = lean_mk_array(v_nbuckets_973_, v___x_975_);
v___x_977_ = lean_array_propagate_mark(v_data_970_, v___x_976_);
v___x_978_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v___x_974_, v_data_970_, v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_m_979_, lean_object* v_a_980_, lean_object* v_b_981_){
_start:
{
lean_object* v_size_982_; lean_object* v_buckets_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1026_; 
v_size_982_ = lean_ctor_get(v_m_979_, 0);
v_buckets_983_ = lean_ctor_get(v_m_979_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_m_979_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_985_ = v_m_979_;
v_isShared_986_ = v_isSharedCheck_1026_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_buckets_983_);
lean_inc(v_size_982_);
lean_dec(v_m_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1026_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; uint64_t v___x_988_; uint64_t v___x_989_; uint64_t v___x_990_; uint64_t v_fold_991_; uint64_t v___x_992_; uint64_t v___x_993_; uint64_t v___x_994_; size_t v___x_995_; size_t v___x_996_; size_t v___x_997_; size_t v___x_998_; size_t v___x_999_; lean_object* v_bkt_1000_; uint8_t v___x_1001_; 
v___x_987_ = lean_array_get_size(v_buckets_983_);
v___x_988_ = l_Lean_ExprStructEq_hash(v_a_980_);
v___x_989_ = 32ULL;
v___x_990_ = lean_uint64_shift_right(v___x_988_, v___x_989_);
v_fold_991_ = lean_uint64_xor(v___x_988_, v___x_990_);
v___x_992_ = 16ULL;
v___x_993_ = lean_uint64_shift_right(v_fold_991_, v___x_992_);
v___x_994_ = lean_uint64_xor(v_fold_991_, v___x_993_);
v___x_995_ = lean_uint64_to_usize(v___x_994_);
v___x_996_ = lean_usize_of_nat(v___x_987_);
v___x_997_ = ((size_t)1ULL);
v___x_998_ = lean_usize_sub(v___x_996_, v___x_997_);
v___x_999_ = lean_usize_land(v___x_995_, v___x_998_);
v_bkt_1000_ = lean_array_uget_borrowed(v_buckets_983_, v___x_999_);
v___x_1001_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_980_, v_bkt_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v_size_x27_1003_; lean_object* v___x_1004_; lean_object* v_buckets_x27_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v_size_x27_1003_ = lean_nat_add(v_size_982_, v___x_1002_);
lean_dec(v_size_982_);
lean_inc(v_bkt_1000_);
v___x_1004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1004_, 0, v_a_980_);
lean_ctor_set(v___x_1004_, 1, v_b_981_);
lean_ctor_set(v___x_1004_, 2, v_bkt_1000_);
v_buckets_x27_1005_ = lean_array_uset(v_buckets_983_, v___x_999_, v___x_1004_);
v___x_1006_ = lean_unsigned_to_nat(4u);
v___x_1007_ = lean_nat_mul(v_size_x27_1003_, v___x_1006_);
v___x_1008_ = lean_unsigned_to_nat(3u);
v___x_1009_ = lean_nat_div(v___x_1007_, v___x_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_array_get_size(v_buckets_x27_1005_);
v___x_1011_ = lean_nat_dec_le(v___x_1009_, v___x_1010_);
lean_dec(v___x_1009_);
if (v___x_1011_ == 0)
{
lean_object* v_val_1012_; lean_object* v___x_1014_; 
v_val_1012_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_buckets_x27_1005_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v_val_1012_);
lean_ctor_set(v___x_985_, 0, v_size_x27_1003_);
v___x_1014_ = v___x_985_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_size_x27_1003_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_val_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_object* v___x_1017_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v_buckets_x27_1005_);
lean_ctor_set(v___x_985_, 0, v_size_x27_1003_);
v___x_1017_ = v___x_985_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_size_x27_1003_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_buckets_x27_1005_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
lean_object* v___x_1019_; lean_object* v_buckets_x27_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_inc(v_bkt_1000_);
v___x_1019_ = lean_box(0);
v_buckets_x27_1020_ = lean_array_uset(v_buckets_983_, v___x_999_, v___x_1019_);
v___x_1021_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_980_, v_b_981_, v_bkt_1000_);
v___x_1022_ = lean_array_uset(v_buckets_x27_1020_, v___x_999_, v___x_1021_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v___x_1022_);
v___x_1024_ = v___x_985_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_size_982_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_1027_, lean_object* v_e_1028_, lean_object* v_fst_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1031_ = lean_st_ref_take(v_a_1027_);
v___x_1032_ = lean_box(0);
v___x_1033_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_1031_, v_e_1028_, v_fst_1029_);
v___x_1034_ = lean_st_ref_put(v_a_1027_, v___x_1033_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_1035_, lean_object* v_e_1036_, lean_object* v_fst_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1035_, v_e_1036_, v_fst_1037_);
lean_dec(v_a_1035_);
return v_res_1039_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = l_Lean_maxRecDepthErrorMessage;
v___x_1046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3);
v___x_1048_ = l_Lean_MessageData_ofFormat(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4);
v___x_1050_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2));
v___x_1051_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v___x_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(lean_object* v_ref_1052_){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_ref_1052_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___boxed(lean_object* v_ref_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object* v_x_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___y_1069_; lean_object* v_toCold_1086_; lean_object* v_currRecDepth_1087_; lean_object* v_ref_1088_; uint16_t v_optionFlags_1089_; uint8_t v_suppressElabErrors_1090_; uint8_t v_checkDeprecated_1091_; uint8_t v_isRecordingDeps_1092_; lean_object* v_maxRecDepth_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v_toCold_1086_ = lean_ctor_get(v___y_1065_, 0);
v_currRecDepth_1087_ = lean_ctor_get(v___y_1065_, 1);
v_ref_1088_ = lean_ctor_get(v___y_1065_, 2);
v_optionFlags_1089_ = lean_ctor_get_uint16(v___y_1065_, sizeof(void*)*3);
v_suppressElabErrors_1090_ = lean_ctor_get_uint8(v___y_1065_, sizeof(void*)*3 + 2);
v_checkDeprecated_1091_ = lean_ctor_get_uint8(v___y_1065_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1092_ = lean_ctor_get_uint8(v___y_1065_, sizeof(void*)*3 + 4);
v_maxRecDepth_1098_ = lean_ctor_get(v_toCold_1086_, 3);
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_nat_dec_eq(v_maxRecDepth_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
uint8_t v___x_1101_; 
v___x_1101_ = lean_nat_dec_eq(v_currRecDepth_1087_, v_maxRecDepth_1098_);
if (v___x_1101_ == 0)
{
goto v___jp_1093_;
}
else
{
lean_object* v___x_1102_; 
lean_dec(v___y_1062_);
lean_dec_ref(v_x_1060_);
lean_inc(v_ref_1088_);
v___x_1102_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1088_);
v___y_1069_ = v___x_1102_;
goto v___jp_1068_;
}
}
else
{
goto v___jp_1093_;
}
v___jp_1068_:
{
if (lean_obj_tag(v___y_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
v_a_1070_ = lean_ctor_get(v___y_1069_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___y_1069_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___y_1069_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___y_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___y_1069_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___y_1069_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___y_1069_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___y_1069_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
v___jp_1093_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_nat_add(v_currRecDepth_1087_, v___x_1094_);
lean_inc(v_ref_1088_);
lean_inc_ref(v_toCold_1086_);
v___x_1096_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1096_, 0, v_toCold_1086_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
lean_ctor_set(v___x_1096_, 2, v_ref_1088_);
lean_ctor_set_uint16(v___x_1096_, sizeof(void*)*3, v_optionFlags_1089_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*3 + 2, v_suppressElabErrors_1090_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*3 + 3, v_checkDeprecated_1091_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*3 + 4, v_isRecordingDeps_1092_);
lean_inc(v___y_1066_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1061_);
v___x_1097_ = lean_apply_7(v_x_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___x_1096_, v___y_1066_, lean_box(0));
v___y_1069_ = v___x_1097_;
goto v___jp_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1104_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(lean_object* v_a_1112_, lean_object* v_x_1113_){
_start:
{
if (lean_obj_tag(v_x_1113_) == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_box(0);
return v___x_1114_;
}
else
{
lean_object* v_key_1115_; lean_object* v_value_1116_; lean_object* v_tail_1117_; uint8_t v___x_1118_; 
v_key_1115_ = lean_ctor_get(v_x_1113_, 0);
v_value_1116_ = lean_ctor_get(v_x_1113_, 1);
v_tail_1117_ = lean_ctor_get(v_x_1113_, 2);
v___x_1118_ = l_Lean_ExprStructEq_beq(v_key_1115_, v_a_1112_);
if (v___x_1118_ == 0)
{
v_x_1113_ = v_tail_1117_;
goto _start;
}
else
{
lean_object* v___x_1120_; 
lean_inc(v_value_1116_);
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_value_1116_);
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(lean_object* v_a_1121_, lean_object* v_x_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1121_, v_x_1122_);
lean_dec(v_x_1122_);
lean_dec_ref(v_a_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_m_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_buckets_1126_; lean_object* v___x_1127_; uint64_t v___x_1128_; uint64_t v___x_1129_; uint64_t v___x_1130_; uint64_t v_fold_1131_; uint64_t v___x_1132_; uint64_t v___x_1133_; uint64_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_buckets_1126_ = lean_ctor_get(v_m_1124_, 1);
v___x_1127_ = lean_array_get_size(v_buckets_1126_);
v___x_1128_ = l_Lean_ExprStructEq_hash(v_a_1125_);
v___x_1129_ = 32ULL;
v___x_1130_ = lean_uint64_shift_right(v___x_1128_, v___x_1129_);
v_fold_1131_ = lean_uint64_xor(v___x_1128_, v___x_1130_);
v___x_1132_ = 16ULL;
v___x_1133_ = lean_uint64_shift_right(v_fold_1131_, v___x_1132_);
v___x_1134_ = lean_uint64_xor(v_fold_1131_, v___x_1133_);
v___x_1135_ = lean_uint64_to_usize(v___x_1134_);
v___x_1136_ = lean_usize_of_nat(v___x_1127_);
v___x_1137_ = ((size_t)1ULL);
v___x_1138_ = lean_usize_sub(v___x_1136_, v___x_1137_);
v___x_1139_ = lean_usize_land(v___x_1135_, v___x_1138_);
v___x_1140_ = lean_array_uget_borrowed(v_buckets_1126_, v___x_1139_);
v___x_1141_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1125_, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_m_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_1142_, v_a_1143_);
lean_dec_ref(v_a_1143_);
lean_dec_ref(v_m_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1145_, lean_object* v_x_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_apply_1(v_x_1146_, lean_box(0));
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___y_1147_);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_x_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1156_, v_x_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1165_, lean_object* v_pre_1166_, lean_object* v_post_1167_, lean_object* v_usedLetOnly_1168_, lean_object* v_skipConstInApp_1169_, lean_object* v_skipInstances_1170_, lean_object* v_body_1171_, lean_object* v_x_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v_usedLetOnly_boxed_1180_; uint8_t v_skipConstInApp_boxed_1181_; uint8_t v_skipInstances_boxed_1182_; lean_object* v_res_1183_; 
v_usedLetOnly_boxed_1180_ = lean_unbox(v_usedLetOnly_1168_);
v_skipConstInApp_boxed_1181_ = lean_unbox(v_skipConstInApp_1169_);
v_skipInstances_boxed_1182_ = lean_unbox(v_skipInstances_1170_);
v_res_1183_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1165_, v_pre_1166_, v_post_1167_, v_usedLetOnly_boxed_1180_, v_skipConstInApp_boxed_1181_, v_skipInstances_boxed_1182_, v_body_1171_, v_x_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1173_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1187_, lean_object* v_pre_1188_, lean_object* v_post_1189_, uint8_t v_usedLetOnly_1190_, uint8_t v_skipConstInApp_1191_, uint8_t v_skipInstances_1192_, lean_object* v_body_1193_, lean_object* v_x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_array_push(v_fvars_1187_, v_x_1194_);
v___x_1203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1188_, v_post_1189_, v_usedLetOnly_1190_, v_skipConstInApp_1191_, v_skipInstances_1192_, v___x_1202_, v_body_1193_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1204_, lean_object* v_pre_1205_, lean_object* v_post_1206_, lean_object* v_usedLetOnly_1207_, lean_object* v_skipConstInApp_1208_, lean_object* v_skipInstances_1209_, lean_object* v_body_1210_, lean_object* v_x_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v_usedLetOnly_boxed_1219_; uint8_t v_skipConstInApp_boxed_1220_; uint8_t v_skipInstances_boxed_1221_; lean_object* v_res_1222_; 
v_usedLetOnly_boxed_1219_ = lean_unbox(v_usedLetOnly_1207_);
v_skipConstInApp_boxed_1220_ = lean_unbox(v_skipConstInApp_1208_);
v_skipInstances_boxed_1221_ = lean_unbox(v_skipInstances_1209_);
v_res_1222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1204_, v_pre_1205_, v_post_1206_, v_usedLetOnly_boxed_1219_, v_skipConstInApp_boxed_1220_, v_skipInstances_boxed_1221_, v_body_1210_, v_x_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1212_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1223_, lean_object* v_post_1224_, uint8_t v_usedLetOnly_1225_, uint8_t v_skipConstInApp_1226_, uint8_t v_skipInstances_1227_, lean_object* v_e_1228_, lean_object* v_a_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; 
lean_inc_ref(v_post_1224_);
lean_inc(v___y_1234_);
lean_inc_ref(v___y_1233_);
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1231_);
lean_inc_ref(v_e_1228_);
v___x_1236_ = lean_apply_7(v_post_1224_, v_e_1228_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, lean_box(0));
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1268_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1268_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1268_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1267_; 
v_fst_1241_ = lean_ctor_get(v_a_1237_, 0);
v_snd_1242_ = lean_ctor_get(v_a_1237_, 1);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_a_1237_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1244_ = v_a_1237_;
v_isShared_1245_ = v_isSharedCheck_1267_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v_a_1237_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1267_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___y_1247_; 
switch(lean_obj_tag(v_fst_1241_))
{
case 0:
{
lean_object* v_e_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1262_; 
lean_del_object(v___x_1244_);
lean_del_object(v___x_1239_);
lean_dec_ref(v_e_1228_);
lean_dec_ref(v_post_1224_);
lean_dec_ref(v_pre_1223_);
v_e_1254_ = lean_ctor_get(v_fst_1241_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_fst_1241_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1256_ = v_fst_1241_;
v_isShared_1257_ = v_isSharedCheck_1262_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_e_1254_);
lean_dec(v_fst_1241_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1262_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_e_1254_);
lean_ctor_set(v___x_1258_, 1, v_snd_1242_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1258_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
case 1:
{
lean_object* v_e_1263_; lean_object* v___x_1264_; 
lean_del_object(v___x_1244_);
lean_del_object(v___x_1239_);
lean_dec_ref(v_e_1228_);
v_e_1263_ = lean_ctor_get(v_fst_1241_, 0);
lean_inc_ref(v_e_1263_);
lean_dec_ref_known(v_fst_1241_, 1);
v___x_1264_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1223_, v_post_1224_, v_usedLetOnly_1225_, v_skipConstInApp_1226_, v_skipInstances_1227_, v_e_1263_, v_a_1229_, v_snd_1242_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
return v___x_1264_;
}
default: 
{
lean_object* v_e_x3f_1265_; 
lean_dec_ref(v_post_1224_);
lean_dec_ref(v_pre_1223_);
v_e_x3f_1265_ = lean_ctor_get(v_fst_1241_, 0);
lean_inc(v_e_x3f_1265_);
lean_dec_ref_known(v_fst_1241_, 1);
if (lean_obj_tag(v_e_x3f_1265_) == 0)
{
v___y_1247_ = v_e_1228_;
goto v___jp_1246_;
}
else
{
lean_object* v_val_1266_; 
lean_dec_ref(v_e_1228_);
v_val_1266_ = lean_ctor_get(v_e_x3f_1265_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v_e_x3f_1265_, 1);
v___y_1247_ = v_val_1266_;
goto v___jp_1246_;
}
}
}
v___jp_1246_:
{
lean_object* v___x_1249_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___y_1247_);
v___x_1249_ = v___x_1244_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___y_1247_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_snd_1242_);
v___x_1249_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1251_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1249_);
v___x_1251_ = v___x_1239_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v_e_1228_);
lean_dec_ref(v_post_1224_);
lean_dec_ref(v_pre_1223_);
v_a_1269_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1236_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1236_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1277_, lean_object* v_post_1278_, uint8_t v_usedLetOnly_1279_, uint8_t v_skipConstInApp_1280_, uint8_t v_skipInstances_1281_, lean_object* v_fvars_1282_, lean_object* v_e_1283_, lean_object* v_a_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
if (lean_obj_tag(v_e_1283_) == 6)
{
lean_object* v_binderName_1291_; lean_object* v_binderType_1292_; lean_object* v_body_1293_; uint8_t v_binderInfo_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___f_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_binderName_1291_ = lean_ctor_get(v_e_1283_, 0);
lean_inc(v_binderName_1291_);
v_binderType_1292_ = lean_ctor_get(v_e_1283_, 1);
lean_inc_ref(v_binderType_1292_);
v_body_1293_ = lean_ctor_get(v_e_1283_, 2);
lean_inc_ref(v_body_1293_);
v_binderInfo_1294_ = lean_ctor_get_uint8(v_e_1283_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1283_, 3);
v___x_1295_ = lean_box(v_usedLetOnly_1279_);
v___x_1296_ = lean_box(v_skipConstInApp_1280_);
v___x_1297_ = lean_box(v_skipInstances_1281_);
lean_inc_ref(v_post_1278_);
lean_inc_ref(v_pre_1277_);
lean_inc_ref(v_fvars_1282_);
v___f_1298_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1298_, 0, v_fvars_1282_);
lean_closure_set(v___f_1298_, 1, v_pre_1277_);
lean_closure_set(v___f_1298_, 2, v_post_1278_);
lean_closure_set(v___f_1298_, 3, v___x_1295_);
lean_closure_set(v___f_1298_, 4, v___x_1296_);
lean_closure_set(v___f_1298_, 5, v___x_1297_);
lean_closure_set(v___f_1298_, 6, v_body_1293_);
v___x_1299_ = lean_expr_instantiate_rev(v_binderType_1292_, v_fvars_1282_);
lean_dec_ref(v_fvars_1282_);
lean_dec_ref(v_binderType_1292_);
v___x_1300_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1277_, v_post_1278_, v_usedLetOnly_1279_, v_skipConstInApp_1280_, v_skipInstances_1281_, v___x_1299_, v_a_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v_fst_1302_ = lean_ctor_get(v_a_1301_, 0);
lean_inc(v_fst_1302_);
v_snd_1303_ = lean_ctor_get(v_a_1301_, 1);
lean_inc(v_snd_1303_);
lean_dec(v_a_1301_);
v___x_1304_ = 0;
v___x_1305_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1291_, v_binderInfo_1294_, v_fst_1302_, v___f_1298_, v___x_1304_, v_a_1284_, v_snd_1303_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1305_;
}
else
{
lean_dec_ref(v___f_1298_);
lean_dec(v_binderName_1291_);
return v___x_1300_;
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_expr_instantiate_rev(v_e_1283_, v_fvars_1282_);
lean_dec_ref(v_e_1283_);
lean_inc_ref(v_post_1278_);
lean_inc_ref(v_pre_1277_);
v___x_1307_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1277_, v_post_1278_, v_usedLetOnly_1279_, v_skipConstInApp_1280_, v_skipInstances_1281_, v___x_1306_, v_a_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v_fst_1309_; lean_object* v_snd_1310_; uint8_t v___x_1311_; uint8_t v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v_fst_1309_ = lean_ctor_get(v_a_1308_, 0);
lean_inc(v_fst_1309_);
v_snd_1310_ = lean_ctor_get(v_a_1308_, 1);
lean_inc(v_snd_1310_);
lean_dec(v_a_1308_);
v___x_1311_ = 0;
v___x_1312_ = 1;
v___x_1313_ = 1;
v___x_1314_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1282_, v_fst_1309_, v___x_1311_, v_usedLetOnly_1279_, v___x_1311_, v___x_1312_, v___x_1313_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec_ref(v_fvars_1282_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1277_, v_post_1278_, v_usedLetOnly_1279_, v_skipConstInApp_1280_, v_skipInstances_1281_, v_a_1315_, v_a_1284_, v_snd_1310_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1316_;
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_snd_1310_);
lean_dec_ref(v_post_1278_);
lean_dec_ref(v_pre_1277_);
v_a_1317_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1314_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1314_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1282_);
lean_dec_ref(v_post_1278_);
lean_dec_ref(v_pre_1277_);
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1325_, lean_object* v_pre_1326_, lean_object* v_post_1327_, uint8_t v_usedLetOnly_1328_, uint8_t v_skipConstInApp_1329_, uint8_t v_skipInstances_1330_, lean_object* v_body_1331_, lean_object* v_x_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_array_push(v_fvars_1325_, v_x_1332_);
v___x_1341_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1326_, v_post_1327_, v_usedLetOnly_1328_, v_skipConstInApp_1329_, v_skipInstances_1330_, v___x_1340_, v_body_1331_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1342_, lean_object* v_pre_1343_, lean_object* v_post_1344_, lean_object* v_usedLetOnly_1345_, lean_object* v_skipConstInApp_1346_, lean_object* v_skipInstances_1347_, lean_object* v_body_1348_, lean_object* v_x_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
uint8_t v_usedLetOnly_boxed_1357_; uint8_t v_skipConstInApp_boxed_1358_; uint8_t v_skipInstances_boxed_1359_; lean_object* v_res_1360_; 
v_usedLetOnly_boxed_1357_ = lean_unbox(v_usedLetOnly_1345_);
v_skipConstInApp_boxed_1358_ = lean_unbox(v_skipConstInApp_1346_);
v_skipInstances_boxed_1359_ = lean_unbox(v_skipInstances_1347_);
v_res_1360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1342_, v_pre_1343_, v_post_1344_, v_usedLetOnly_boxed_1357_, v_skipConstInApp_boxed_1358_, v_skipInstances_boxed_1359_, v_body_1348_, v_x_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1350_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1361_, lean_object* v_post_1362_, uint8_t v_usedLetOnly_1363_, uint8_t v_skipConstInApp_1364_, uint8_t v_skipInstances_1365_, lean_object* v_fvars_1366_, lean_object* v_e_1367_, lean_object* v_a_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
if (lean_obj_tag(v_e_1367_) == 8)
{
lean_object* v_declName_1375_; lean_object* v_type_1376_; lean_object* v_value_1377_; lean_object* v_body_1378_; uint8_t v_nondep_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_declName_1375_ = lean_ctor_get(v_e_1367_, 0);
lean_inc(v_declName_1375_);
v_type_1376_ = lean_ctor_get(v_e_1367_, 1);
lean_inc_ref(v_type_1376_);
v_value_1377_ = lean_ctor_get(v_e_1367_, 2);
lean_inc_ref(v_value_1377_);
v_body_1378_ = lean_ctor_get(v_e_1367_, 3);
lean_inc_ref(v_body_1378_);
v_nondep_1379_ = lean_ctor_get_uint8(v_e_1367_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1367_, 4);
v___x_1380_ = lean_box(v_usedLetOnly_1363_);
v___x_1381_ = lean_box(v_skipConstInApp_1364_);
v___x_1382_ = lean_box(v_skipInstances_1365_);
lean_inc_ref_n(v_post_1362_, 2);
lean_inc_ref_n(v_pre_1361_, 2);
lean_inc_ref(v_fvars_1366_);
v___f_1383_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1383_, 0, v_fvars_1366_);
lean_closure_set(v___f_1383_, 1, v_pre_1361_);
lean_closure_set(v___f_1383_, 2, v_post_1362_);
lean_closure_set(v___f_1383_, 3, v___x_1380_);
lean_closure_set(v___f_1383_, 4, v___x_1381_);
lean_closure_set(v___f_1383_, 5, v___x_1382_);
lean_closure_set(v___f_1383_, 6, v_body_1378_);
v___x_1384_ = lean_expr_instantiate_rev(v_type_1376_, v_fvars_1366_);
lean_dec_ref(v_type_1376_);
v___x_1385_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1361_, v_post_1362_, v_usedLetOnly_1363_, v_skipConstInApp_1364_, v_skipInstances_1365_, v___x_1384_, v_a_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v_fst_1387_; lean_object* v_snd_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v_fst_1387_ = lean_ctor_get(v_a_1386_, 0);
lean_inc(v_fst_1387_);
v_snd_1388_ = lean_ctor_get(v_a_1386_, 1);
lean_inc(v_snd_1388_);
lean_dec(v_a_1386_);
v___x_1389_ = lean_expr_instantiate_rev(v_value_1377_, v_fvars_1366_);
lean_dec_ref(v_fvars_1366_);
lean_dec_ref(v_value_1377_);
v___x_1390_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1361_, v_post_1362_, v_usedLetOnly_1363_, v_skipConstInApp_1364_, v_skipInstances_1365_, v___x_1389_, v_a_1368_, v_snd_1388_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v_fst_1392_; lean_object* v_snd_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v_fst_1392_ = lean_ctor_get(v_a_1391_, 0);
lean_inc(v_fst_1392_);
v_snd_1393_ = lean_ctor_get(v_a_1391_, 1);
lean_inc(v_snd_1393_);
lean_dec(v_a_1391_);
v___x_1394_ = 0;
v___x_1395_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1375_, v_fst_1387_, v_fst_1392_, v___f_1383_, v_nondep_1379_, v___x_1394_, v_a_1368_, v_snd_1393_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
return v___x_1395_;
}
else
{
lean_dec(v_fst_1387_);
lean_dec_ref(v___f_1383_);
lean_dec(v_declName_1375_);
return v___x_1390_;
}
}
else
{
lean_dec_ref(v___f_1383_);
lean_dec_ref(v_value_1377_);
lean_dec(v_declName_1375_);
lean_dec_ref(v_fvars_1366_);
lean_dec_ref(v_post_1362_);
lean_dec_ref(v_pre_1361_);
return v___x_1385_;
}
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_expr_instantiate_rev(v_e_1367_, v_fvars_1366_);
lean_dec_ref(v_e_1367_);
lean_inc_ref(v_post_1362_);
lean_inc_ref(v_pre_1361_);
v___x_1397_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1361_, v_post_1362_, v_usedLetOnly_1363_, v_skipConstInApp_1364_, v_skipInstances_1365_, v___x_1396_, v_a_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; uint8_t v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v_fst_1399_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_fst_1399_);
v_snd_1400_ = lean_ctor_get(v_a_1398_, 1);
lean_inc(v_snd_1400_);
lean_dec(v_a_1398_);
v___x_1401_ = 0;
v___x_1402_ = 1;
v___x_1403_ = l_Lean_Meta_mkLetFVars(v_fvars_1366_, v_fst_1399_, v_usedLetOnly_1363_, v___x_1401_, v___x_1402_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec_ref(v_fvars_1366_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
v___x_1405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1361_, v_post_1362_, v_usedLetOnly_1363_, v_skipConstInApp_1364_, v_skipInstances_1365_, v_a_1404_, v_a_1368_, v_snd_1400_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
return v___x_1405_;
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec(v_snd_1400_);
lean_dec_ref(v_post_1362_);
lean_dec_ref(v_pre_1361_);
v_a_1406_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1403_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1403_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1366_);
lean_dec_ref(v_post_1362_);
lean_dec_ref(v_pre_1361_);
return v___x_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_pre_1414_, lean_object* v_post_1415_, uint8_t v_usedLetOnly_1416_, uint8_t v_skipConstInApp_1417_, uint8_t v_skipInstances_1418_, size_t v_sz_1419_, size_t v_i_1420_, lean_object* v_bs_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_usize_dec_lt(v_i_1420_, v_sz_1419_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1414_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_bs_1421_);
lean_ctor_set(v___x_1430_, 1, v___y_1423_);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
else
{
lean_object* v_v_1432_; lean_object* v___x_1433_; lean_object* v_bs_x27_1434_; lean_object* v___x_1435_; 
v_v_1432_ = lean_array_uget(v_bs_1421_, v_i_1420_);
v___x_1433_ = lean_unsigned_to_nat(0u);
v_bs_x27_1434_ = lean_array_uset(v_bs_1421_, v_i_1420_, v___x_1433_);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1414_);
v___x_1435_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1414_, v_post_1415_, v_usedLetOnly_1416_, v_skipConstInApp_1417_, v_skipInstances_1418_, v_v_1432_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v_fst_1437_; lean_object* v_snd_1438_; size_t v___x_1439_; size_t v___x_1440_; lean_object* v___x_1441_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v_fst_1437_ = lean_ctor_get(v_a_1436_, 0);
lean_inc(v_fst_1437_);
v_snd_1438_ = lean_ctor_get(v_a_1436_, 1);
lean_inc(v_snd_1438_);
lean_dec(v_a_1436_);
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_add(v_i_1420_, v___x_1439_);
v___x_1441_ = lean_array_uset(v_bs_x27_1434_, v_i_1420_, v_fst_1437_);
v_i_1420_ = v___x_1440_;
v_bs_1421_ = v___x_1441_;
v___y_1423_ = v_snd_1438_;
goto _start;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v_bs_x27_1434_);
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1414_);
v_a_1443_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1435_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1435_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object* v_pre_1451_, lean_object* v_post_1452_, uint8_t v_usedLetOnly_1453_, uint8_t v_skipConstInApp_1454_, uint8_t v_skipInstances_1455_, lean_object* v___x_1456_, lean_object* v___y_1457_, lean_object* v_b_1458_, lean_object* v_a_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1451_, v_post_1452_, v_usedLetOnly_1453_, v_skipConstInApp_1454_, v_skipInstances_1455_, v___x_1456_, v___y_1457_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1485_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1485_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1485_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_fst_1471_; lean_object* v_snd_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1484_; 
v_fst_1471_ = lean_ctor_get(v_a_1467_, 0);
v_snd_1472_ = lean_ctor_get(v_a_1467_, 1);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_a_1467_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1474_ = v_a_1467_;
v_isShared_1475_ = v_isSharedCheck_1484_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_snd_1472_);
lean_inc(v_fst_1471_);
lean_dec(v_a_1467_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1484_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1476_ = lean_array_fset(v_b_1458_, v_a_1459_, v_fst_1471_);
v___x_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1477_);
v___x_1479_ = v___x_1474_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_snd_1472_);
v___x_1479_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1481_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1479_);
v___x_1481_ = v___x_1469_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v_b_1458_);
v_a_1486_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1466_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1466_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v_pre_1494_, lean_object* v_post_1495_, lean_object* v_usedLetOnly_1496_, lean_object* v_skipConstInApp_1497_, lean_object* v_skipInstances_1498_, lean_object* v___x_1499_, lean_object* v___y_1500_, lean_object* v_b_1501_, lean_object* v_a_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v_usedLetOnly_boxed_1509_; uint8_t v_skipConstInApp_boxed_1510_; uint8_t v_skipInstances_boxed_1511_; lean_object* v_res_1512_; 
v_usedLetOnly_boxed_1509_ = lean_unbox(v_usedLetOnly_1496_);
v_skipConstInApp_boxed_1510_ = lean_unbox(v_skipConstInApp_1497_);
v_skipInstances_boxed_1511_ = lean_unbox(v_skipInstances_1498_);
v_res_1512_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1494_, v_post_1495_, v_usedLetOnly_boxed_1509_, v_skipConstInApp_boxed_1510_, v_skipInstances_boxed_1511_, v___x_1499_, v___y_1500_, v_b_1501_, v_a_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v_a_1502_);
lean_dec(v___y_1500_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object* v_upperBound_1513_, lean_object* v___x_1514_, lean_object* v_pre_1515_, lean_object* v_post_1516_, uint8_t v_usedLetOnly_1517_, uint8_t v_skipConstInApp_1518_, uint8_t v_skipInstances_1519_, lean_object* v_a_1520_, lean_object* v_b_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___y_1530_; uint8_t v___x_1564_; 
v___x_1564_ = lean_nat_dec_lt(v_a_1520_, v_upperBound_1513_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v_a_1520_);
lean_dec_ref(v_post_1516_);
lean_dec_ref(v_pre_1515_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_b_1521_);
lean_ctor_set(v___x_1565_, 1, v___y_1523_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1567_ = lean_array_fget_borrowed(v_b_1521_, v_a_1520_);
v___x_1568_ = lean_array_get_size(v___x_1514_);
v___x_1569_ = lean_nat_dec_lt(v_a_1520_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___f_1573_; 
lean_inc(v___x_1567_);
v___x_1570_ = lean_box(v_usedLetOnly_1517_);
v___x_1571_ = lean_box(v_skipConstInApp_1518_);
v___x_1572_ = lean_box(v_skipInstances_1519_);
lean_inc(v_a_1520_);
lean_inc(v___y_1522_);
lean_inc_ref(v_post_1516_);
lean_inc_ref(v_pre_1515_);
v___f_1573_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1573_, 0, v_pre_1515_);
lean_closure_set(v___f_1573_, 1, v_post_1516_);
lean_closure_set(v___f_1573_, 2, v___x_1570_);
lean_closure_set(v___f_1573_, 3, v___x_1571_);
lean_closure_set(v___f_1573_, 4, v___x_1572_);
lean_closure_set(v___f_1573_, 5, v___x_1567_);
lean_closure_set(v___f_1573_, 6, v___y_1522_);
lean_closure_set(v___f_1573_, 7, v_b_1521_);
lean_closure_set(v___f_1573_, 8, v_a_1520_);
v___y_1530_ = v___f_1573_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1574_; uint8_t v_isInstance_1575_; 
v___x_1574_ = lean_array_fget_borrowed(v___x_1514_, v_a_1520_);
v_isInstance_1575_ = lean_ctor_get_uint8(v___x_1574_, sizeof(void*)*1 + 4);
if (v_isInstance_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___f_1579_; 
lean_inc(v___x_1567_);
v___x_1576_ = lean_box(v_usedLetOnly_1517_);
v___x_1577_ = lean_box(v_skipConstInApp_1518_);
v___x_1578_ = lean_box(v_skipInstances_1519_);
lean_inc(v_a_1520_);
lean_inc(v___y_1522_);
lean_inc_ref(v_post_1516_);
lean_inc_ref(v_pre_1515_);
v___f_1579_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1579_, 0, v_pre_1515_);
lean_closure_set(v___f_1579_, 1, v_post_1516_);
lean_closure_set(v___f_1579_, 2, v___x_1576_);
lean_closure_set(v___f_1579_, 3, v___x_1577_);
lean_closure_set(v___f_1579_, 4, v___x_1578_);
lean_closure_set(v___f_1579_, 5, v___x_1567_);
lean_closure_set(v___f_1579_, 6, v___y_1522_);
lean_closure_set(v___f_1579_, 7, v_b_1521_);
lean_closure_set(v___f_1579_, 8, v_a_1520_);
v___y_1530_ = v___f_1579_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1580_; lean_object* v___f_1581_; 
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_b_1521_);
v___f_1581_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1581_, 0, v___x_1580_);
v___y_1530_ = v___f_1581_;
goto v___jp_1529_;
}
}
}
v___jp_1529_:
{
lean_object* v___x_1531_; 
lean_inc(v___y_1527_);
lean_inc_ref(v___y_1526_);
lean_inc(v___y_1525_);
lean_inc_ref(v___y_1524_);
v___x_1531_ = lean_apply_6(v___y_1530_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, lean_box(0));
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1555_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1534_ = v___x_1531_;
v_isShared_1535_ = v_isSharedCheck_1555_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1531_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1555_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v_fst_1536_; 
v_fst_1536_ = lean_ctor_get(v_a_1532_, 0);
lean_inc(v_fst_1536_);
if (lean_obj_tag(v_fst_1536_) == 0)
{
lean_object* v_snd_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_a_1520_);
lean_dec_ref(v_post_1516_);
lean_dec_ref(v_pre_1515_);
v_snd_1537_ = lean_ctor_get(v_a_1532_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_a_1532_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v_a_1532_, 0);
lean_dec(v_unused_1549_);
v___x_1539_ = v_a_1532_;
v_isShared_1540_ = v_isSharedCheck_1548_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_snd_1537_);
lean_dec(v_a_1532_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1548_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_a_1541_; lean_object* v___x_1543_; 
v_a_1541_ = lean_ctor_get(v_fst_1536_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v_fst_1536_, 1);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v_a_1541_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_snd_1537_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1543_);
v___x_1545_ = v___x_1534_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v_snd_1550_; lean_object* v_a_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_del_object(v___x_1534_);
v_snd_1550_ = lean_ctor_get(v_a_1532_, 1);
lean_inc(v_snd_1550_);
lean_dec(v_a_1532_);
v_a_1551_ = lean_ctor_get(v_fst_1536_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v_fst_1536_, 1);
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_nat_add(v_a_1520_, v___x_1552_);
lean_dec(v_a_1520_);
v_a_1520_ = v___x_1553_;
v_b_1521_ = v_a_1551_;
v___y_1523_ = v_snd_1550_;
goto _start;
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_a_1520_);
lean_dec_ref(v_post_1516_);
lean_dec_ref(v_pre_1515_);
v_a_1556_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1531_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1531_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1582_, lean_object* v_pre_1583_, lean_object* v_post_1584_, uint8_t v_usedLetOnly_1585_, uint8_t v_skipConstInApp_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_f_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; 
if (lean_obj_tag(v_x_1587_) == 5)
{
lean_object* v_fn_1653_; lean_object* v_arg_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_fn_1653_ = lean_ctor_get(v_x_1587_, 0);
lean_inc_ref(v_fn_1653_);
v_arg_1654_ = lean_ctor_get(v_x_1587_, 1);
lean_inc_ref(v_arg_1654_);
lean_dec_ref_known(v_x_1587_, 2);
v___x_1655_ = lean_array_set(v_x_1588_, v_x_1589_, v_arg_1654_);
v___x_1656_ = lean_unsigned_to_nat(1u);
v___x_1657_ = lean_nat_sub(v_x_1589_, v___x_1656_);
lean_dec(v_x_1589_);
v_x_1587_ = v_fn_1653_;
v_x_1588_ = v___x_1655_;
v_x_1589_ = v___x_1657_;
goto _start;
}
else
{
lean_dec(v_x_1589_);
if (v_skipConstInApp_1586_ == 0)
{
goto v___jp_1648_;
}
else
{
uint8_t v___x_1659_; 
v___x_1659_ = l_Lean_Expr_isConst(v_x_1587_);
if (v___x_1659_ == 0)
{
goto v___jp_1648_;
}
else
{
v_f_1598_ = v_x_1587_;
v___y_1599_ = v___y_1590_;
v___y_1600_ = v___y_1591_;
v___y_1601_ = v___y_1592_;
v___y_1602_ = v___y_1593_;
v___y_1603_ = v___y_1594_;
v___y_1604_ = v___y_1595_;
goto v___jp_1597_;
}
}
}
v___jp_1597_:
{
if (v_skipInstances_1582_ == 0)
{
size_t v_sz_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
v_sz_1605_ = lean_array_size(v_x_1588_);
v___x_1606_ = ((size_t)0ULL);
lean_inc_ref(v_post_1584_);
lean_inc_ref(v_pre_1583_);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1583_, v_post_1584_, v_usedLetOnly_1585_, v_skipConstInApp_1586_, v_skipInstances_1582_, v_sz_1605_, v___x_1606_, v_x_1588_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v_fst_1609_; lean_object* v_snd_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v_fst_1609_ = lean_ctor_get(v_a_1608_, 0);
lean_inc(v_fst_1609_);
v_snd_1610_ = lean_ctor_get(v_a_1608_, 1);
lean_inc(v_snd_1610_);
lean_dec(v_a_1608_);
v___x_1611_ = l_Lean_mkAppN(v_f_1598_, v_fst_1609_);
lean_dec(v_fst_1609_);
v___x_1612_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1583_, v_post_1584_, v_usedLetOnly_1585_, v_skipConstInApp_1586_, v_skipInstances_1582_, v___x_1611_, v___y_1599_, v_snd_1610_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
return v___x_1612_;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v_f_1598_);
lean_dec_ref(v_post_1584_);
lean_dec_ref(v_pre_1583_);
v_a_1613_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1607_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1607_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_array_get_size(v_x_1588_);
lean_inc_ref(v_f_1598_);
v___x_1622_ = l_Lean_Meta_getFunInfoNArgs(v_f_1598_, v___x_1621_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v_paramInfo_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v_paramInfo_1624_ = lean_ctor_get(v_a_1623_, 0);
lean_inc_ref(v_paramInfo_1624_);
lean_dec(v_a_1623_);
v___x_1625_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1584_);
lean_inc_ref(v_pre_1583_);
v___x_1626_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_1621_, v_paramInfo_1624_, v_pre_1583_, v_post_1584_, v_usedLetOnly_1585_, v_skipConstInApp_1586_, v_skipInstances_1582_, v___x_1625_, v_x_1588_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec_ref(v_paramInfo_1624_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v_fst_1628_; lean_object* v_snd_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v_fst_1628_ = lean_ctor_get(v_a_1627_, 0);
lean_inc(v_fst_1628_);
v_snd_1629_ = lean_ctor_get(v_a_1627_, 1);
lean_inc(v_snd_1629_);
lean_dec(v_a_1627_);
v___x_1630_ = l_Lean_mkAppN(v_f_1598_, v_fst_1628_);
lean_dec(v_fst_1628_);
v___x_1631_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1583_, v_post_1584_, v_usedLetOnly_1585_, v_skipConstInApp_1586_, v_skipInstances_1582_, v___x_1630_, v___y_1599_, v_snd_1629_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
return v___x_1631_;
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v_f_1598_);
lean_dec_ref(v_post_1584_);
lean_dec_ref(v_pre_1583_);
v_a_1632_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1626_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1626_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v___y_1600_);
lean_dec_ref(v_f_1598_);
lean_dec_ref(v_x_1588_);
lean_dec_ref(v_post_1584_);
lean_dec_ref(v_pre_1583_);
v_a_1640_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1622_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1622_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
v___jp_1648_:
{
lean_object* v___x_1649_; 
lean_inc_ref(v_post_1584_);
lean_inc_ref(v_pre_1583_);
v___x_1649_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1583_, v_post_1584_, v_usedLetOnly_1585_, v_skipConstInApp_1586_, v_skipInstances_1582_, v_x_1587_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v_fst_1651_; lean_object* v_snd_1652_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v_fst_1651_ = lean_ctor_get(v_a_1650_, 0);
lean_inc(v_fst_1651_);
v_snd_1652_ = lean_ctor_get(v_a_1650_, 1);
lean_inc(v_snd_1652_);
lean_dec(v_a_1650_);
v_f_1598_ = v_fst_1651_;
v___y_1599_ = v___y_1590_;
v___y_1600_ = v_snd_1652_;
v___y_1601_ = v___y_1592_;
v___y_1602_ = v___y_1593_;
v___y_1603_ = v___y_1594_;
v___y_1604_ = v___y_1595_;
goto v___jp_1597_;
}
else
{
lean_dec_ref(v_x_1588_);
lean_dec_ref(v_post_1584_);
lean_dec_ref(v_pre_1583_);
return v___x_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1660_, lean_object* v_pre_1661_, lean_object* v_e_1662_, lean_object* v_post_1663_, uint8_t v_usedLetOnly_1664_, uint8_t v_skipConstInApp_1665_, uint8_t v_skipInstances_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_Core_checkSystem(v___x_1660_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v___x_1675_; 
lean_dec_ref_known(v___x_1674_, 1);
lean_inc_ref(v_pre_1661_);
lean_inc(v___y_1672_);
lean_inc_ref(v___y_1671_);
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
lean_inc_ref(v_e_1662_);
v___x_1675_ = lean_apply_7(v_pre_1661_, v_e_1662_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, lean_box(0));
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1737_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1737_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1737_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v_fst_1680_; lean_object* v_snd_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1736_; 
v_fst_1680_ = lean_ctor_get(v_a_1676_, 0);
v_snd_1681_ = lean_ctor_get(v_a_1676_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_a_1676_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1683_ = v_a_1676_;
v_isShared_1684_ = v_isSharedCheck_1736_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_snd_1681_);
lean_inc(v_fst_1680_);
lean_dec(v_a_1676_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1736_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___y_1686_; 
switch(lean_obj_tag(v_fst_1680_))
{
case 0:
{
lean_object* v_e_1725_; lean_object* v___x_1727_; 
lean_dec_ref(v_post_1663_);
lean_dec_ref(v_e_1662_);
lean_dec_ref(v_pre_1661_);
v_e_1725_ = lean_ctor_get(v_fst_1680_, 0);
lean_inc_ref(v_e_1725_);
lean_dec_ref_known(v_fst_1680_, 1);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v_e_1725_);
v___x_1727_ = v___x_1683_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_e_1725_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_snd_1681_);
v___x_1727_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1729_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1727_);
v___x_1729_ = v___x_1678_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
case 1:
{
lean_object* v_e_1732_; lean_object* v___x_1733_; 
lean_del_object(v___x_1683_);
lean_del_object(v___x_1678_);
lean_dec_ref(v_e_1662_);
v_e_1732_ = lean_ctor_get(v_fst_1680_, 0);
lean_inc_ref(v_e_1732_);
lean_dec_ref_known(v_fst_1680_, 1);
v___x_1733_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v_e_1732_, v___y_1667_, v_snd_1681_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1733_;
}
default: 
{
lean_object* v_e_x3f_1734_; 
lean_del_object(v___x_1683_);
lean_del_object(v___x_1678_);
v_e_x3f_1734_ = lean_ctor_get(v_fst_1680_, 0);
lean_inc(v_e_x3f_1734_);
lean_dec_ref_known(v_fst_1680_, 1);
if (lean_obj_tag(v_e_x3f_1734_) == 0)
{
v___y_1686_ = v_e_1662_;
goto v___jp_1685_;
}
else
{
lean_object* v_val_1735_; 
lean_dec_ref(v_e_1662_);
v_val_1735_ = lean_ctor_get(v_e_x3f_1734_, 0);
lean_inc(v_val_1735_);
lean_dec_ref_known(v_e_x3f_1734_, 1);
v___y_1686_ = v_val_1735_;
goto v___jp_1685_;
}
}
}
v___jp_1685_:
{
switch(lean_obj_tag(v___y_1686_))
{
case 7:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1688_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v___x_1687_, v___y_1686_, v___y_1667_, v_snd_1681_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1688_;
}
case 6:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1690_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v___x_1689_, v___y_1686_, v___y_1667_, v_snd_1681_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1690_;
}
case 8:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v___x_1691_, v___y_1686_, v___y_1667_, v_snd_1681_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1692_;
}
case 5:
{
lean_object* v_dummy_1693_; lean_object* v_nargs_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_dummy_1693_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1694_ = l_Lean_Expr_getAppNumArgs(v___y_1686_);
lean_inc(v_nargs_1694_);
v___x_1695_ = lean_mk_array(v_nargs_1694_, v_dummy_1693_);
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_sub(v_nargs_1694_, v___x_1696_);
lean_dec(v_nargs_1694_);
v___x_1698_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1666_, v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v___y_1686_, v___x_1695_, v___x_1697_, v___y_1667_, v_snd_1681_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1698_;
}
case 10:
{
lean_object* v_data_1699_; lean_object* v_expr_1700_; lean_object* v___x_1701_; 
v_data_1699_ = lean_ctor_get(v___y_1686_, 0);
v_expr_1700_ = lean_ctor_get(v___y_1686_, 1);
lean_inc_ref(v_expr_1700_);
lean_inc_ref(v_post_1663_);
lean_inc_ref(v_pre_1661_);
v___x_1701_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v_expr_1700_, v___y_1667_, v_snd_1681_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v_fst_1703_; lean_object* v_snd_1704_; size_t v___x_1705_; size_t v___x_1706_; uint8_t v___x_1707_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v_fst_1703_ = lean_ctor_get(v_a_1702_, 0);
lean_inc(v_fst_1703_);
v_snd_1704_ = lean_ctor_get(v_a_1702_, 1);
lean_inc(v_snd_1704_);
lean_dec(v_a_1702_);
v___x_1705_ = lean_ptr_addr(v_expr_1700_);
v___x_1706_ = lean_ptr_addr(v_fst_1703_);
v___x_1707_ = lean_usize_dec_eq(v___x_1705_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_inc(v_data_1699_);
lean_dec_ref_known(v___y_1686_, 2);
v___x_1708_ = l_Lean_Expr_mdata___override(v_data_1699_, v_fst_1703_);
v___x_1709_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v___x_1708_, v___y_1667_, v_snd_1704_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1709_;
}
else
{
lean_object* v___x_1710_; 
lean_dec(v_fst_1703_);
v___x_1710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v___y_1686_, v___y_1667_, v_snd_1704_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1710_;
}
}
else
{
lean_dec_ref_known(v___y_1686_, 2);
lean_dec_ref(v_post_1663_);
lean_dec_ref(v_pre_1661_);
return v___x_1701_;
}
}
case 11:
{
lean_object* v_typeName_1711_; lean_object* v_idx_1712_; lean_object* v_struct_1713_; lean_object* v___x_1714_; 
v_typeName_1711_ = lean_ctor_get(v___y_1686_, 0);
v_idx_1712_ = lean_ctor_get(v___y_1686_, 1);
v_struct_1713_ = lean_ctor_get(v___y_1686_, 2);
lean_inc_ref(v_struct_1713_);
lean_inc_ref(v_post_1663_);
lean_inc_ref(v_pre_1661_);
v___x_1714_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v_struct_1713_, v___y_1667_, v_snd_1681_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v_fst_1716_; lean_object* v_snd_1717_; size_t v___x_1718_; size_t v___x_1719_; uint8_t v___x_1720_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v_fst_1716_ = lean_ctor_get(v_a_1715_, 0);
lean_inc(v_fst_1716_);
v_snd_1717_ = lean_ctor_get(v_a_1715_, 1);
lean_inc(v_snd_1717_);
lean_dec(v_a_1715_);
v___x_1718_ = lean_ptr_addr(v_struct_1713_);
v___x_1719_ = lean_ptr_addr(v_fst_1716_);
v___x_1720_ = lean_usize_dec_eq(v___x_1718_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_inc(v_idx_1712_);
lean_inc(v_typeName_1711_);
lean_dec_ref_known(v___y_1686_, 3);
v___x_1721_ = l_Lean_Expr_proj___override(v_typeName_1711_, v_idx_1712_, v_fst_1716_);
v___x_1722_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v___x_1721_, v___y_1667_, v_snd_1717_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; 
lean_dec(v_fst_1716_);
v___x_1723_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v___y_1686_, v___y_1667_, v_snd_1717_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1723_;
}
}
else
{
lean_dec_ref_known(v___y_1686_, 3);
lean_dec_ref(v_post_1663_);
lean_dec_ref(v_pre_1661_);
return v___x_1714_;
}
}
default: 
{
lean_object* v___x_1724_; 
v___x_1724_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1661_, v_post_1663_, v_usedLetOnly_1664_, v_skipConstInApp_1665_, v_skipInstances_1666_, v___y_1686_, v___y_1667_, v_snd_1681_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1724_;
}
}
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref(v_post_1663_);
lean_dec_ref(v_e_1662_);
lean_dec_ref(v_pre_1661_);
v_a_1738_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1675_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1675_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v___y_1668_);
lean_dec_ref(v_post_1663_);
lean_dec_ref(v_e_1662_);
lean_dec_ref(v_pre_1661_);
v_a_1746_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1674_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1674_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1754_, lean_object* v_pre_1755_, lean_object* v_e_1756_, lean_object* v_post_1757_, lean_object* v_usedLetOnly_1758_, lean_object* v_skipConstInApp_1759_, lean_object* v_skipInstances_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v_usedLetOnly_boxed_1768_; uint8_t v_skipConstInApp_boxed_1769_; uint8_t v_skipInstances_boxed_1770_; lean_object* v_res_1771_; 
v_usedLetOnly_boxed_1768_ = lean_unbox(v_usedLetOnly_1758_);
v_skipConstInApp_boxed_1769_ = lean_unbox(v_skipConstInApp_1759_);
v_skipInstances_boxed_1770_ = lean_unbox(v_skipInstances_1760_);
v_res_1771_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1754_, v_pre_1755_, v_e_1756_, v_post_1757_, v_usedLetOnly_boxed_1768_, v_skipConstInApp_boxed_1769_, v_skipInstances_boxed_1770_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1761_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1772_, lean_object* v_post_1773_, uint8_t v_usedLetOnly_1774_, uint8_t v_skipConstInApp_1775_, uint8_t v_skipInstances_1776_, lean_object* v_e_1777_, lean_object* v_a_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_inc(v_a_1778_);
v___x_1785_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1785_, 0, lean_box(0));
lean_closure_set(v___x_1785_, 1, lean_box(0));
lean_closure_set(v___x_1785_, 2, v_a_1778_);
v___x_1786_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1785_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1841_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1841_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1841_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_fst_1791_; lean_object* v_snd_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1840_; 
v_fst_1791_ = lean_ctor_get(v_a_1787_, 0);
v_snd_1792_ = lean_ctor_get(v_a_1787_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_a_1787_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1794_ = v_a_1787_;
v_isShared_1795_ = v_isSharedCheck_1840_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_snd_1792_);
lean_inc(v_fst_1791_);
lean_dec(v_a_1787_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1840_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1791_, v_e_1777_);
lean_dec(v_fst_1791_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___f_1801_; lean_object* v___x_1802_; 
lean_del_object(v___x_1794_);
lean_del_object(v___x_1789_);
v___x_1797_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1798_ = lean_box(v_usedLetOnly_1774_);
v___x_1799_ = lean_box(v_skipConstInApp_1775_);
v___x_1800_ = lean_box(v_skipInstances_1776_);
lean_inc_ref(v_e_1777_);
v___f_1801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1801_, 0, v___x_1797_);
lean_closure_set(v___f_1801_, 1, v_pre_1772_);
lean_closure_set(v___f_1801_, 2, v_e_1777_);
lean_closure_set(v___f_1801_, 3, v_post_1773_);
lean_closure_set(v___f_1801_, 4, v___x_1798_);
lean_closure_set(v___f_1801_, 5, v___x_1799_);
lean_closure_set(v___f_1801_, 6, v___x_1800_);
v___x_1802_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1801_, v_a_1778_, v_snd_1792_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v_fst_1804_; lean_object* v_snd_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v_fst_1804_ = lean_ctor_get(v_a_1803_, 0);
lean_inc_n(v_fst_1804_, 2);
v_snd_1805_ = lean_ctor_get(v_a_1803_, 1);
lean_inc(v_snd_1805_);
lean_dec(v_a_1803_);
lean_inc(v_a_1778_);
v___f_1806_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1806_, 0, v_a_1778_);
lean_closure_set(v___f_1806_, 1, v_e_1777_);
lean_closure_set(v___f_1806_, 2, v_fst_1804_);
v___x_1807_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1806_, v_snd_1805_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1824_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1824_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1824_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_snd_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1822_; 
v_snd_1812_ = lean_ctor_get(v_a_1808_, 1);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_a_1808_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v_a_1808_, 0);
lean_dec(v_unused_1823_);
v___x_1814_ = v_a_1808_;
v_isShared_1815_ = v_isSharedCheck_1822_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_snd_1812_);
lean_dec(v_a_1808_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1822_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_fst_1804_);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_fst_1804_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_snd_1812_);
v___x_1817_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1817_);
v___x_1819_ = v___x_1810_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_fst_1804_);
v_a_1825_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1807_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1807_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
else
{
lean_dec_ref(v_e_1777_);
return v___x_1802_;
}
}
else
{
lean_object* v_val_1833_; lean_object* v___x_1835_; 
lean_dec_ref(v_e_1777_);
lean_dec_ref(v_post_1773_);
lean_dec_ref(v_pre_1772_);
v_val_1833_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v___x_1796_, 1);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v_val_1833_);
v___x_1835_ = v___x_1794_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_val_1833_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_snd_1792_);
v___x_1835_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1835_);
v___x_1837_ = v___x_1789_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec_ref(v_e_1777_);
lean_dec_ref(v_post_1773_);
lean_dec_ref(v_pre_1772_);
v_a_1842_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1786_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1786_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1850_, lean_object* v_post_1851_, uint8_t v_usedLetOnly_1852_, uint8_t v_skipConstInApp_1853_, uint8_t v_skipInstances_1854_, lean_object* v_fvars_1855_, lean_object* v_e_1856_, lean_object* v_a_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
if (lean_obj_tag(v_e_1856_) == 7)
{
lean_object* v_binderName_1864_; lean_object* v_binderType_1865_; lean_object* v_body_1866_; uint8_t v_binderInfo_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___f_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_binderName_1864_ = lean_ctor_get(v_e_1856_, 0);
lean_inc(v_binderName_1864_);
v_binderType_1865_ = lean_ctor_get(v_e_1856_, 1);
lean_inc_ref(v_binderType_1865_);
v_body_1866_ = lean_ctor_get(v_e_1856_, 2);
lean_inc_ref(v_body_1866_);
v_binderInfo_1867_ = lean_ctor_get_uint8(v_e_1856_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1856_, 3);
v___x_1868_ = lean_box(v_usedLetOnly_1852_);
v___x_1869_ = lean_box(v_skipConstInApp_1853_);
v___x_1870_ = lean_box(v_skipInstances_1854_);
lean_inc_ref(v_post_1851_);
lean_inc_ref(v_pre_1850_);
lean_inc_ref(v_fvars_1855_);
v___f_1871_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1871_, 0, v_fvars_1855_);
lean_closure_set(v___f_1871_, 1, v_pre_1850_);
lean_closure_set(v___f_1871_, 2, v_post_1851_);
lean_closure_set(v___f_1871_, 3, v___x_1868_);
lean_closure_set(v___f_1871_, 4, v___x_1869_);
lean_closure_set(v___f_1871_, 5, v___x_1870_);
lean_closure_set(v___f_1871_, 6, v_body_1866_);
v___x_1872_ = lean_expr_instantiate_rev(v_binderType_1865_, v_fvars_1855_);
lean_dec_ref(v_fvars_1855_);
lean_dec_ref(v_binderType_1865_);
v___x_1873_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1850_, v_post_1851_, v_usedLetOnly_1852_, v_skipConstInApp_1853_, v_skipInstances_1854_, v___x_1872_, v_a_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v_fst_1875_; lean_object* v_snd_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1873_, 1);
v_fst_1875_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_fst_1875_);
v_snd_1876_ = lean_ctor_get(v_a_1874_, 1);
lean_inc(v_snd_1876_);
lean_dec(v_a_1874_);
v___x_1877_ = 0;
v___x_1878_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1864_, v_binderInfo_1867_, v_fst_1875_, v___f_1871_, v___x_1877_, v_a_1857_, v_snd_1876_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
return v___x_1878_;
}
else
{
lean_dec_ref(v___f_1871_);
lean_dec(v_binderName_1864_);
return v___x_1873_;
}
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_expr_instantiate_rev(v_e_1856_, v_fvars_1855_);
lean_dec_ref(v_e_1856_);
lean_inc_ref(v_post_1851_);
lean_inc_ref(v_pre_1850_);
v___x_1880_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1850_, v_post_1851_, v_usedLetOnly_1852_, v_skipConstInApp_1853_, v_skipInstances_1854_, v___x_1879_, v_a_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_fst_1882_; lean_object* v_snd_1883_; uint8_t v___x_1884_; uint8_t v___x_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v_fst_1882_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_fst_1882_);
v_snd_1883_ = lean_ctor_get(v_a_1881_, 1);
lean_inc(v_snd_1883_);
lean_dec(v_a_1881_);
v___x_1884_ = 0;
v___x_1885_ = 1;
v___x_1886_ = 1;
v___x_1887_ = l_Lean_Meta_mkForallFVars(v_fvars_1855_, v_fst_1882_, v___x_1884_, v_usedLetOnly_1852_, v___x_1885_, v___x_1886_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec_ref(v_fvars_1855_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1889_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1850_, v_post_1851_, v_usedLetOnly_1852_, v_skipConstInApp_1853_, v_skipInstances_1854_, v_a_1888_, v_a_1857_, v_snd_1883_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
return v___x_1889_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_snd_1883_);
lean_dec_ref(v_post_1851_);
lean_dec_ref(v_pre_1850_);
v_a_1890_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1887_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1887_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1855_);
lean_dec_ref(v_post_1851_);
lean_dec_ref(v_pre_1850_);
return v___x_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1898_, lean_object* v_pre_1899_, lean_object* v_post_1900_, uint8_t v_usedLetOnly_1901_, uint8_t v_skipConstInApp_1902_, uint8_t v_skipInstances_1903_, lean_object* v_body_1904_, lean_object* v_x_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_array_push(v_fvars_1898_, v_x_1905_);
v___x_1914_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1899_, v_post_1900_, v_usedLetOnly_1901_, v_skipConstInApp_1902_, v_skipInstances_1903_, v___x_1913_, v_body_1904_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_1915_, lean_object* v_post_1916_, lean_object* v_usedLetOnly_1917_, lean_object* v_skipConstInApp_1918_, lean_object* v_skipInstances_1919_, lean_object* v_sz_1920_, lean_object* v_i_1921_, lean_object* v_bs_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
uint8_t v_usedLetOnly_boxed_1930_; uint8_t v_skipConstInApp_boxed_1931_; uint8_t v_skipInstances_boxed_1932_; size_t v_sz_boxed_1933_; size_t v_i_boxed_1934_; lean_object* v_res_1935_; 
v_usedLetOnly_boxed_1930_ = lean_unbox(v_usedLetOnly_1917_);
v_skipConstInApp_boxed_1931_ = lean_unbox(v_skipConstInApp_1918_);
v_skipInstances_boxed_1932_ = lean_unbox(v_skipInstances_1919_);
v_sz_boxed_1933_ = lean_unbox_usize(v_sz_1920_);
lean_dec(v_sz_1920_);
v_i_boxed_1934_ = lean_unbox_usize(v_i_1921_);
lean_dec(v_i_1921_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1915_, v_post_1916_, v_usedLetOnly_boxed_1930_, v_skipConstInApp_boxed_1931_, v_skipInstances_boxed_1932_, v_sz_boxed_1933_, v_i_boxed_1934_, v_bs_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1923_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1936_, lean_object* v_post_1937_, lean_object* v_usedLetOnly_1938_, lean_object* v_skipConstInApp_1939_, lean_object* v_skipInstances_1940_, lean_object* v_e_1941_, lean_object* v_a_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
uint8_t v_usedLetOnly_boxed_1949_; uint8_t v_skipConstInApp_boxed_1950_; uint8_t v_skipInstances_boxed_1951_; lean_object* v_res_1952_; 
v_usedLetOnly_boxed_1949_ = lean_unbox(v_usedLetOnly_1938_);
v_skipConstInApp_boxed_1950_ = lean_unbox(v_skipConstInApp_1939_);
v_skipInstances_boxed_1951_ = lean_unbox(v_skipInstances_1940_);
v_res_1952_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1936_, v_post_1937_, v_usedLetOnly_boxed_1949_, v_skipConstInApp_boxed_1950_, v_skipInstances_boxed_1951_, v_e_1941_, v_a_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v_a_1942_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1953_, lean_object* v_post_1954_, lean_object* v_usedLetOnly_1955_, lean_object* v_skipConstInApp_1956_, lean_object* v_skipInstances_1957_, lean_object* v_fvars_1958_, lean_object* v_e_1959_, lean_object* v_a_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
uint8_t v_usedLetOnly_boxed_1967_; uint8_t v_skipConstInApp_boxed_1968_; uint8_t v_skipInstances_boxed_1969_; lean_object* v_res_1970_; 
v_usedLetOnly_boxed_1967_ = lean_unbox(v_usedLetOnly_1955_);
v_skipConstInApp_boxed_1968_ = lean_unbox(v_skipConstInApp_1956_);
v_skipInstances_boxed_1969_ = lean_unbox(v_skipInstances_1957_);
v_res_1970_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1953_, v_post_1954_, v_usedLetOnly_boxed_1967_, v_skipConstInApp_boxed_1968_, v_skipInstances_boxed_1969_, v_fvars_1958_, v_e_1959_, v_a_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v_a_1960_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1971_, lean_object* v_post_1972_, lean_object* v_usedLetOnly_1973_, lean_object* v_skipConstInApp_1974_, lean_object* v_skipInstances_1975_, lean_object* v_fvars_1976_, lean_object* v_e_1977_, lean_object* v_a_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
uint8_t v_usedLetOnly_boxed_1985_; uint8_t v_skipConstInApp_boxed_1986_; uint8_t v_skipInstances_boxed_1987_; lean_object* v_res_1988_; 
v_usedLetOnly_boxed_1985_ = lean_unbox(v_usedLetOnly_1973_);
v_skipConstInApp_boxed_1986_ = lean_unbox(v_skipConstInApp_1974_);
v_skipInstances_boxed_1987_ = lean_unbox(v_skipInstances_1975_);
v_res_1988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1971_, v_post_1972_, v_usedLetOnly_boxed_1985_, v_skipConstInApp_boxed_1986_, v_skipInstances_boxed_1987_, v_fvars_1976_, v_e_1977_, v_a_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v_a_1978_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1989_, lean_object* v_post_1990_, lean_object* v_usedLetOnly_1991_, lean_object* v_skipConstInApp_1992_, lean_object* v_skipInstances_1993_, lean_object* v_e_1994_, lean_object* v_a_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
uint8_t v_usedLetOnly_boxed_2002_; uint8_t v_skipConstInApp_boxed_2003_; uint8_t v_skipInstances_boxed_2004_; lean_object* v_res_2005_; 
v_usedLetOnly_boxed_2002_ = lean_unbox(v_usedLetOnly_1991_);
v_skipConstInApp_boxed_2003_ = lean_unbox(v_skipConstInApp_1992_);
v_skipInstances_boxed_2004_ = lean_unbox(v_skipInstances_1993_);
v_res_2005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1989_, v_post_1990_, v_usedLetOnly_boxed_2002_, v_skipConstInApp_boxed_2003_, v_skipInstances_boxed_2004_, v_e_1994_, v_a_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v_a_1995_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_2006_, lean_object* v_post_2007_, lean_object* v_usedLetOnly_2008_, lean_object* v_skipConstInApp_2009_, lean_object* v_skipInstances_2010_, lean_object* v_fvars_2011_, lean_object* v_e_2012_, lean_object* v_a_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v_usedLetOnly_boxed_2020_; uint8_t v_skipConstInApp_boxed_2021_; uint8_t v_skipInstances_boxed_2022_; lean_object* v_res_2023_; 
v_usedLetOnly_boxed_2020_ = lean_unbox(v_usedLetOnly_2008_);
v_skipConstInApp_boxed_2021_ = lean_unbox(v_skipConstInApp_2009_);
v_skipInstances_boxed_2022_ = lean_unbox(v_skipInstances_2010_);
v_res_2023_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_2006_, v_post_2007_, v_usedLetOnly_boxed_2020_, v_skipConstInApp_boxed_2021_, v_skipInstances_boxed_2022_, v_fvars_2011_, v_e_2012_, v_a_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v_a_2013_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_2024_, lean_object* v___x_2025_, lean_object* v_pre_2026_, lean_object* v_post_2027_, lean_object* v_usedLetOnly_2028_, lean_object* v_skipConstInApp_2029_, lean_object* v_skipInstances_2030_, lean_object* v_a_2031_, lean_object* v_b_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
uint8_t v_usedLetOnly_boxed_2040_; uint8_t v_skipConstInApp_boxed_2041_; uint8_t v_skipInstances_boxed_2042_; lean_object* v_res_2043_; 
v_usedLetOnly_boxed_2040_ = lean_unbox(v_usedLetOnly_2028_);
v_skipConstInApp_boxed_2041_ = lean_unbox(v_skipConstInApp_2029_);
v_skipInstances_boxed_2042_ = lean_unbox(v_skipInstances_2030_);
v_res_2043_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2024_, v___x_2025_, v_pre_2026_, v_post_2027_, v_usedLetOnly_boxed_2040_, v_skipConstInApp_boxed_2041_, v_skipInstances_boxed_2042_, v_a_2031_, v_b_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2033_);
lean_dec_ref(v___x_2025_);
lean_dec(v_upperBound_2024_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2044_, lean_object* v_pre_2045_, lean_object* v_post_2046_, lean_object* v_usedLetOnly_2047_, lean_object* v_skipConstInApp_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v_skipInstances_boxed_2059_; uint8_t v_usedLetOnly_boxed_2060_; uint8_t v_skipConstInApp_boxed_2061_; lean_object* v_res_2062_; 
v_skipInstances_boxed_2059_ = lean_unbox(v_skipInstances_2044_);
v_usedLetOnly_boxed_2060_ = lean_unbox(v_usedLetOnly_2047_);
v_skipConstInApp_boxed_2061_ = lean_unbox(v_skipConstInApp_2048_);
v_res_2062_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2059_, v_pre_2045_, v_post_2046_, v_usedLetOnly_boxed_2060_, v_skipConstInApp_boxed_2061_, v_x_2049_, v_x_2050_, v_x_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2052_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2063_, lean_object* v_x_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_apply_1(v_x_2064_, lean_box(0));
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v___y_2065_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2074_, lean_object* v_x_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2074_, v_x_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2082_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_unsigned_to_nat(16u);
v___x_2085_ = lean_mk_array(v___x_2084_, v___x_2083_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___x_2086_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2090_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2090_, 0, lean_box(0));
lean_closure_set(v___x_2090_, 1, lean_box(0));
lean_closure_set(v___x_2090_, 2, v___x_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2091_, lean_object* v_pre_2092_, lean_object* v_post_2093_, uint8_t v_usedLetOnly_2094_, uint8_t v_skipConstInApp_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v_a_2105_; lean_object* v_fst_2106_; lean_object* v_snd_2107_; lean_object* v___x_2108_; 
v___x_2102_ = 0;
v___x_2103_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2104_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2103_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v_fst_2106_ = lean_ctor_get(v_a_2105_, 0);
lean_inc(v_fst_2106_);
v_snd_2107_ = lean_ctor_get(v_a_2105_, 1);
lean_inc(v_snd_2107_);
lean_dec(v_a_2105_);
v___x_2108_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2092_, v_post_2093_, v_usedLetOnly_2094_, v_skipConstInApp_2095_, v___x_2102_, v_input_2091_, v_fst_2106_, v_snd_2107_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v_fst_2110_; lean_object* v_snd_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2130_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v_fst_2110_ = lean_ctor_get(v_a_2109_, 0);
lean_inc(v_fst_2110_);
v_snd_2111_ = lean_ctor_get(v_a_2109_, 1);
lean_inc(v_snd_2111_);
lean_dec(v_a_2109_);
v___x_2112_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2112_, 0, lean_box(0));
lean_closure_set(v___x_2112_, 1, lean_box(0));
lean_closure_set(v___x_2112_, 2, v_fst_2106_);
v___x_2113_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2112_, v_snd_2111_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2130_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2130_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v_snd_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2128_; 
v_snd_2118_ = lean_ctor_get(v_a_2114_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_a_2114_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; 
v_unused_2129_ = lean_ctor_get(v_a_2114_, 0);
lean_dec(v_unused_2129_);
v___x_2120_ = v_a_2114_;
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_snd_2118_);
lean_dec(v_a_2114_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v_fst_2110_);
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_fst_2110_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_snd_2118_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2123_);
v___x_2125_ = v___x_2116_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
else
{
lean_dec(v_fst_2106_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2131_, lean_object* v_pre_2132_, lean_object* v_post_2133_, lean_object* v_usedLetOnly_2134_, lean_object* v_skipConstInApp_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
uint8_t v_usedLetOnly_boxed_2142_; uint8_t v_skipConstInApp_boxed_2143_; lean_object* v_res_2144_; 
v_usedLetOnly_boxed_2142_ = lean_unbox(v_usedLetOnly_2134_);
v_skipConstInApp_boxed_2143_ = lean_unbox(v_skipConstInApp_2135_);
v_res_2144_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2131_, v_pre_2132_, v_post_2133_, v_usedLetOnly_boxed_2142_, v_skipConstInApp_boxed_2143_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v___y_2154_; lean_object* v___x_2171_; uint8_t v_transparency_2172_; lean_object* v___f_2173_; lean_object* v___f_2174_; uint8_t v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2171_ = l_Lean_Meta_Context_config(v_a_2148_);
v_transparency_2172_ = lean_ctor_get_uint8(v___x_2171_, 9);
lean_dec_ref(v___x_2171_);
v___f_2173_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2174_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2175_ = 0;
v___x_2176_ = 3;
v___x_2177_ = lean_box(0);
v___x_2178_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2172_, v___x_2176_);
if (v___x_2178_ == 0)
{
lean_object* v_keyedConfig_2179_; uint8_t v_trackZetaDelta_2180_; lean_object* v_zetaDeltaSet_2181_; lean_object* v_lctx_2182_; lean_object* v_localInstances_2183_; lean_object* v_defEqCtx_x3f_2184_; lean_object* v_synthPendingDepth_2185_; lean_object* v_customCanUnfoldPredicate_x3f_2186_; uint8_t v_univApprox_2187_; uint8_t v_inTypeClassResolution_2188_; uint8_t v_cacheInferType_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_keyedConfig_2179_ = lean_ctor_get(v_a_2148_, 0);
v_trackZetaDelta_2180_ = lean_ctor_get_uint8(v_a_2148_, sizeof(void*)*7);
v_zetaDeltaSet_2181_ = lean_ctor_get(v_a_2148_, 1);
v_lctx_2182_ = lean_ctor_get(v_a_2148_, 2);
v_localInstances_2183_ = lean_ctor_get(v_a_2148_, 3);
v_defEqCtx_x3f_2184_ = lean_ctor_get(v_a_2148_, 4);
v_synthPendingDepth_2185_ = lean_ctor_get(v_a_2148_, 5);
v_customCanUnfoldPredicate_x3f_2186_ = lean_ctor_get(v_a_2148_, 6);
v_univApprox_2187_ = lean_ctor_get_uint8(v_a_2148_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2188_ = lean_ctor_get_uint8(v_a_2148_, sizeof(void*)*7 + 2);
v_cacheInferType_2189_ = lean_ctor_get_uint8(v_a_2148_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2179_);
v___x_2190_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2176_, v_keyedConfig_2179_);
lean_inc(v_customCanUnfoldPredicate_x3f_2186_);
lean_inc(v_synthPendingDepth_2185_);
lean_inc(v_defEqCtx_x3f_2184_);
lean_inc_ref(v_localInstances_2183_);
lean_inc_ref(v_lctx_2182_);
lean_inc(v_zetaDeltaSet_2181_);
v___x_2191_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v_zetaDeltaSet_2181_);
lean_ctor_set(v___x_2191_, 2, v_lctx_2182_);
lean_ctor_set(v___x_2191_, 3, v_localInstances_2183_);
lean_ctor_set(v___x_2191_, 4, v_defEqCtx_x3f_2184_);
lean_ctor_set(v___x_2191_, 5, v_synthPendingDepth_2185_);
lean_ctor_set(v___x_2191_, 6, v_customCanUnfoldPredicate_x3f_2186_);
lean_ctor_set_uint8(v___x_2191_, sizeof(void*)*7, v_trackZetaDelta_2180_);
lean_ctor_set_uint8(v___x_2191_, sizeof(void*)*7 + 1, v_univApprox_2187_);
lean_ctor_set_uint8(v___x_2191_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2188_);
lean_ctor_set_uint8(v___x_2191_, sizeof(void*)*7 + 3, v_cacheInferType_2189_);
v___x_2192_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2147_, v___f_2174_, v___f_2173_, v___x_2175_, v___x_2175_, v___x_2177_, v___x_2191_, v_a_2149_, v_a_2150_, v_a_2151_);
lean_dec_ref_known(v___x_2191_, 7);
v___y_2154_ = v___x_2192_;
goto v___jp_2153_;
}
else
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2147_, v___f_2174_, v___f_2173_, v___x_2175_, v___x_2175_, v___x_2177_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
v___y_2154_ = v___x_2193_;
goto v___jp_2153_;
}
v___jp_2153_:
{
if (lean_obj_tag(v___y_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
v_a_2155_ = lean_ctor_get(v___y_2154_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___y_2154_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___y_2154_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___y_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
v_a_2163_ = lean_ctor_get(v___y_2154_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___y_2154_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___y_2154_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___y_2154_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2201_, lean_object* v_m_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2202_, v_a_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2205_, lean_object* v_m_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2205_, v_m_2206_, v_a_2207_);
lean_dec(v_a_2207_);
lean_dec_ref(v_m_2206_);
return v_res_2208_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
uint8_t v___x_2212_; 
v___x_2212_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2210_, v_x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_){
_start:
{
uint8_t v_res_2216_; lean_object* v_r_2217_; 
v_res_2216_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2213_, v_x_2214_, v_x_2215_);
lean_dec_ref(v_x_2215_);
lean_dec_ref(v_x_2214_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2218_, lean_object* v_a_2219_, lean_object* v_x_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2219_, v_x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2222_, lean_object* v_a_2223_, lean_object* v_x_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2222_, v_a_2223_, v_x_2224_);
lean_dec(v_x_2224_);
lean_dec(v_a_2223_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2226_, lean_object* v___x_2227_, lean_object* v_pre_2228_, lean_object* v_post_2229_, uint8_t v_usedLetOnly_2230_, uint8_t v_skipConstInApp_2231_, uint8_t v_skipInstances_2232_, lean_object* v___x_2233_, lean_object* v_inst_2234_, lean_object* v_R_2235_, lean_object* v_a_2236_, lean_object* v_b_2237_, lean_object* v_c_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2226_, v___x_2227_, v_pre_2228_, v_post_2229_, v_usedLetOnly_2230_, v_skipConstInApp_2231_, v_skipInstances_2232_, v_a_2236_, v_b_2237_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2247_ = _args[0];
lean_object* v___x_2248_ = _args[1];
lean_object* v_pre_2249_ = _args[2];
lean_object* v_post_2250_ = _args[3];
lean_object* v_usedLetOnly_2251_ = _args[4];
lean_object* v_skipConstInApp_2252_ = _args[5];
lean_object* v_skipInstances_2253_ = _args[6];
lean_object* v___x_2254_ = _args[7];
lean_object* v_inst_2255_ = _args[8];
lean_object* v_R_2256_ = _args[9];
lean_object* v_a_2257_ = _args[10];
lean_object* v_b_2258_ = _args[11];
lean_object* v_c_2259_ = _args[12];
lean_object* v___y_2260_ = _args[13];
lean_object* v___y_2261_ = _args[14];
lean_object* v___y_2262_ = _args[15];
lean_object* v___y_2263_ = _args[16];
lean_object* v___y_2264_ = _args[17];
lean_object* v___y_2265_ = _args[18];
lean_object* v___y_2266_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2267_; uint8_t v_skipConstInApp_boxed_2268_; uint8_t v_skipInstances_boxed_2269_; lean_object* v_res_2270_; 
v_usedLetOnly_boxed_2267_ = lean_unbox(v_usedLetOnly_2251_);
v_skipConstInApp_boxed_2268_ = lean_unbox(v_skipConstInApp_2252_);
v_skipInstances_boxed_2269_ = lean_unbox(v_skipInstances_2253_);
v_res_2270_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2247_, v___x_2248_, v_pre_2249_, v_post_2250_, v_usedLetOnly_boxed_2267_, v_skipConstInApp_boxed_2268_, v_skipInstances_boxed_2269_, v___x_2254_, v_inst_2255_, v_R_2256_, v_a_2257_, v_b_2258_, v_c_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2260_);
lean_dec(v___x_2254_);
lean_dec_ref(v___x_2248_);
lean_dec(v_upperBound_2247_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2271_, lean_object* v_m_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2272_, v_a_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2275_, lean_object* v_m_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2275_, v_m_2276_, v_a_2277_);
lean_dec_ref(v_a_2277_);
lean_dec_ref(v_m_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2279_, lean_object* v_name_2280_, uint8_t v_bi_2281_, lean_object* v_type_2282_, lean_object* v_k_2283_, uint8_t v_kind_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2280_, v_bi_2281_, v_type_2282_, v_k_2283_, v_kind_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2293_, lean_object* v_name_2294_, lean_object* v_bi_2295_, lean_object* v_type_2296_, lean_object* v_k_2297_, lean_object* v_kind_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
uint8_t v_bi_boxed_2306_; uint8_t v_kind_boxed_2307_; lean_object* v_res_2308_; 
v_bi_boxed_2306_ = lean_unbox(v_bi_2295_);
v_kind_boxed_2307_ = lean_unbox(v_kind_2298_);
v_res_2308_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2293_, v_name_2294_, v_bi_boxed_2306_, v_type_2296_, v_k_2297_, v_kind_boxed_2307_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2299_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2309_, lean_object* v_name_2310_, lean_object* v_type_2311_, lean_object* v_val_2312_, lean_object* v_k_2313_, uint8_t v_nondep_2314_, uint8_t v_kind_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2310_, v_type_2311_, v_val_2312_, v_k_2313_, v_nondep_2314_, v_kind_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2324_, lean_object* v_name_2325_, lean_object* v_type_2326_, lean_object* v_val_2327_, lean_object* v_k_2328_, lean_object* v_nondep_2329_, lean_object* v_kind_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
uint8_t v_nondep_boxed_2338_; uint8_t v_kind_boxed_2339_; lean_object* v_res_2340_; 
v_nondep_boxed_2338_ = lean_unbox(v_nondep_2329_);
v_kind_boxed_2339_ = lean_unbox(v_kind_2330_);
v_res_2340_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2324_, v_name_2325_, v_type_2326_, v_val_2327_, v_k_2328_, v_nondep_boxed_2338_, v_kind_boxed_2339_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2331_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2341_, lean_object* v_ref_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2342_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2349_, lean_object* v_ref_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2349_, v_ref_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2357_, lean_object* v_x_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2367_, lean_object* v_x_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2367_, v_x_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2369_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2377_, lean_object* v_m_2378_, lean_object* v_a_2379_, lean_object* v_b_2380_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2378_, v_a_2379_, v_b_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2382_, lean_object* v_x_2383_, size_t v_x_2384_, lean_object* v_x_2385_){
_start:
{
uint8_t v___x_2386_; 
v___x_2386_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2383_, v_x_2384_, v_x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2387_, lean_object* v_x_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_){
_start:
{
size_t v_x_39388__boxed_2391_; uint8_t v_res_2392_; lean_object* v_r_2393_; 
v_x_39388__boxed_2391_ = lean_unbox_usize(v_x_2389_);
lean_dec(v_x_2389_);
v_res_2392_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2387_, v_x_2388_, v_x_39388__boxed_2391_, v_x_2390_);
lean_dec_ref(v_x_2390_);
lean_dec_ref(v_x_2388_);
v_r_2393_ = lean_box(v_res_2392_);
return v_r_2393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object* v_00_u03b2_2394_, lean_object* v_a_2395_, lean_object* v_x_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_2395_, v_x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object* v_00_u03b2_2398_, lean_object* v_a_2399_, lean_object* v_x_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_2398_, v_a_2399_, v_x_2400_);
lean_dec(v_x_2400_);
lean_dec_ref(v_a_2399_);
return v_res_2401_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2402_, lean_object* v_a_2403_, lean_object* v_x_2404_){
_start:
{
uint8_t v___x_2405_; 
v___x_2405_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2403_, v_x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2406_, lean_object* v_a_2407_, lean_object* v_x_2408_){
_start:
{
uint8_t v_res_2409_; lean_object* v_r_2410_; 
v_res_2409_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2406_, v_a_2407_, v_x_2408_);
lean_dec(v_x_2408_);
lean_dec_ref(v_a_2407_);
v_r_2410_ = lean_box(v_res_2409_);
return v_r_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2411_, lean_object* v_data_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2414_, lean_object* v_a_2415_, lean_object* v_b_2416_, lean_object* v_x_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2415_, v_b_2416_, v_x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2419_, lean_object* v_keys_2420_, lean_object* v_vals_2421_, lean_object* v_heq_2422_, lean_object* v_i_2423_, lean_object* v_k_2424_){
_start:
{
uint8_t v___x_2425_; 
v___x_2425_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2420_, v_i_2423_, v_k_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2426_, lean_object* v_keys_2427_, lean_object* v_vals_2428_, lean_object* v_heq_2429_, lean_object* v_i_2430_, lean_object* v_k_2431_){
_start:
{
uint8_t v_res_2432_; lean_object* v_r_2433_; 
v_res_2432_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2426_, v_keys_2427_, v_vals_2428_, v_heq_2429_, v_i_2430_, v_k_2431_);
lean_dec_ref(v_k_2431_);
lean_dec_ref(v_vals_2428_);
lean_dec_ref(v_keys_2427_);
v_r_2433_ = lean_box(v_res_2432_);
return v_r_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2434_, lean_object* v_i_2435_, lean_object* v_source_2436_, lean_object* v_target_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2435_, v_source_2436_, v_target_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2439_, lean_object* v_x_2440_, lean_object* v_x_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2440_, v_x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2443_, lean_object* v_decl_2444_, lean_object* v_ref_2445_){
_start:
{
lean_object* v_defValue_2447_; lean_object* v_descr_2448_; lean_object* v_deprecation_x3f_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_defValue_2447_ = lean_ctor_get(v_decl_2444_, 0);
v_descr_2448_ = lean_ctor_get(v_decl_2444_, 1);
v_deprecation_x3f_2449_ = lean_ctor_get(v_decl_2444_, 2);
v___x_2450_ = lean_alloc_ctor(1, 0, 1);
v___x_2451_ = lean_unbox(v_defValue_2447_);
lean_ctor_set_uint8(v___x_2450_, 0, v___x_2451_);
lean_inc(v_deprecation_x3f_2449_);
lean_inc_ref(v_descr_2448_);
lean_inc_n(v_name_2443_, 2);
v___x_2452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2452_, 0, v_name_2443_);
lean_ctor_set(v___x_2452_, 1, v_ref_2445_);
lean_ctor_set(v___x_2452_, 2, v___x_2450_);
lean_ctor_set(v___x_2452_, 3, v_descr_2448_);
lean_ctor_set(v___x_2452_, 4, v_deprecation_x3f_2449_);
v___x_2453_ = lean_register_option(v_name_2443_, v___x_2452_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2461_; 
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v___x_2453_, 0);
lean_dec(v_unused_2462_);
v___x_2455_ = v___x_2453_;
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
else
{
lean_dec(v___x_2453_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
lean_inc(v_defValue_2447_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v_name_2443_);
lean_ctor_set(v___x_2457_, 1, v_defValue_2447_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2457_);
v___x_2459_ = v___x_2455_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_name_2443_);
v_a_2463_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2453_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2453_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2471_, lean_object* v_decl_2472_, lean_object* v_ref_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2471_, v_decl_2472_, v_ref_2473_);
lean_dec_ref(v_decl_2472_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2490_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2491_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2492_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2493_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2490_, v___x_2491_, v___x_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_ref_2502_; lean_object* v___x_2503_; lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2512_; 
v_ref_2502_ = lean_ctor_get(v___y_2499_, 2);
v___x_2503_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
lean_inc(v_ref_2502_);
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_ref_2502_);
lean_ctor_set(v___x_2508_, 1, v_a_2504_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set_tag(v___x_2506_, 1);
lean_ctor_set(v___x_2506_, 0, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2519_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2528_ = l_Lean_stringToMessageData(v___x_2527_);
return v___x_2528_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2531_ = l_Lean_stringToMessageData(v___x_2530_);
return v___x_2531_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2534_ = l_Lean_stringToMessageData(v___x_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2535_, lean_object* v_expectedType_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v___x_2542_; 
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
lean_inc(v_a_2538_);
lean_inc_ref(v_a_2537_);
lean_inc_ref(v_expr_2535_);
v___x_2542_ = lean_infer_type(v_expr_2535_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2544_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_n(v_a_2543_, 2);
lean_dec_ref_known(v___x_2542_, 1);
v___x_2544_ = l_Lean_Meta_getLevel(v_a_2543_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2546_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2544_, 1);
lean_inc_ref(v_expectedType_2536_);
v___x_2546_ = l_Lean_Meta_getLevel(v_expectedType_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v___x_2548_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2549_ = lean_box(0);
v___x_2550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2550_, 0, v_a_2547_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2551_, 0, v_a_2545_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
lean_inc_ref(v___x_2551_);
v___x_2552_ = l_Lean_mkConst(v___x_2548_, v___x_2551_);
v___x_2553_ = lean_unsigned_to_nat(3u);
v___x_2554_ = lean_mk_empty_array_with_capacity(v___x_2553_);
lean_inc(v_a_2543_);
v___x_2555_ = lean_array_push(v___x_2554_, v_a_2543_);
lean_inc_ref(v_expr_2535_);
v___x_2556_ = lean_array_push(v___x_2555_, v_expr_2535_);
lean_inc_ref(v_expectedType_2536_);
v___x_2557_ = lean_array_push(v___x_2556_, v_expectedType_2536_);
v___x_2558_ = l_Lean_mkAppN(v___x_2552_, v___x_2557_);
lean_dec_ref(v___x_2557_);
v___x_2559_ = lean_box(0);
v___x_2560_ = l_Lean_Meta_trySynthInstance(v___x_2558_, v___x_2559_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2658_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2658_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2658_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
switch(lean_obj_tag(v_a_2561_))
{
case 0:
{
lean_object* v___x_2565_; lean_object* v___x_2567_; 
lean_dec_ref_known(v___x_2551_, 2);
lean_dec(v_a_2543_);
lean_dec_ref(v_expectedType_2536_);
lean_dec_ref(v_expr_2535_);
v___x_2565_ = lean_box(0);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2565_);
v___x_2567_ = v___x_2563_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
case 1:
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2653_; 
lean_del_object(v___x_2563_);
v_a_2569_ = lean_ctor_get(v_a_2561_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_a_2561_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2571_ = v_a_2561_;
v_isShared_2572_ = v_isSharedCheck_2653_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v_a_2561_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2653_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2573_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2574_ = l_Lean_mkConst(v___x_2573_, v___x_2551_);
v___x_2575_ = lean_unsigned_to_nat(4u);
v___x_2576_ = lean_mk_empty_array_with_capacity(v___x_2575_);
v___x_2577_ = lean_array_push(v___x_2576_, v_a_2543_);
lean_inc_ref(v_expr_2535_);
v___x_2578_ = lean_array_push(v___x_2577_, v_expr_2535_);
lean_inc_ref(v_expectedType_2536_);
v___x_2579_ = lean_array_push(v___x_2578_, v_expectedType_2536_);
v___x_2580_ = lean_array_push(v___x_2579_, v_a_2569_);
v___x_2581_ = l_Lean_mkAppN(v___x_2574_, v___x_2580_);
lean_dec_ref(v___x_2580_);
v___x_2582_ = l_Lean_Meta_expandCoe(v___x_2581_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2644_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2644_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2644_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v_fst_2594_; lean_object* v___x_2595_; 
v_fst_2594_ = lean_ctor_get(v_a_2583_, 0);
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
lean_inc(v_a_2538_);
lean_inc_ref(v_a_2537_);
lean_inc(v_fst_2594_);
v___x_2595_ = lean_infer_type(v_fst_2594_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
lean_inc_ref(v_expectedType_2536_);
v___x_2597_ = l_Lean_Meta_isExprDefEq(v_a_2596_, v_expectedType_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; uint8_t v___x_2599_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = lean_unbox(v_a_2598_);
lean_dec(v_a_2598_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2625_; 
lean_inc(v_fst_2594_);
lean_del_object(v___x_2585_);
lean_del_object(v___x_2571_);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_a_2583_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; lean_object* v_unused_2627_; 
v_unused_2626_ = lean_ctor_get(v_a_2583_, 1);
lean_dec(v_unused_2626_);
v_unused_2627_ = lean_ctor_get(v_a_2583_, 0);
lean_dec(v_unused_2627_);
v___x_2601_ = v_a_2583_;
v_isShared_2602_ = v_isSharedCheck_2625_;
goto v_resetjp_2600_;
}
else
{
lean_dec(v_a_2583_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2625_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2603_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2604_ = l_Lean_indentExpr(v_expr_2535_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set_tag(v___x_2601_, 7);
lean_ctor_set(v___x_2601_, 1, v___x_2604_);
lean_ctor_set(v___x_2601_, 0, v___x_2603_);
v___x_2606_ = v___x_2601_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
v___x_2607_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = l_Lean_indentExpr(v_expectedType_2536_);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2610_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = l_Lean_indentExpr(v_fst_2594_);
v___x_2614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2614_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
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
}
}
else
{
lean_dec_ref(v_expectedType_2536_);
lean_dec_ref(v_expr_2535_);
goto v___jp_2587_;
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_del_object(v___x_2585_);
lean_dec(v_a_2583_);
lean_del_object(v___x_2571_);
lean_dec_ref(v_expectedType_2536_);
lean_dec_ref(v_expr_2535_);
v_a_2628_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2597_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2597_);
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
lean_del_object(v___x_2585_);
lean_dec(v_a_2583_);
lean_del_object(v___x_2571_);
lean_dec_ref(v_expectedType_2536_);
lean_dec_ref(v_expr_2535_);
v_a_2636_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2595_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2595_);
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
v___jp_2587_:
{
lean_object* v___x_2589_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v_a_2583_);
v___x_2589_ = v___x_2571_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2583_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2591_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2589_);
v___x_2591_ = v___x_2585_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
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
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_del_object(v___x_2571_);
lean_dec_ref(v_expectedType_2536_);
lean_dec_ref(v_expr_2535_);
v_a_2645_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2582_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2582_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
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
default: 
{
lean_object* v___x_2654_; lean_object* v___x_2656_; 
lean_dec_ref_known(v___x_2551_, 2);
lean_dec(v_a_2543_);
lean_dec_ref(v_expectedType_2536_);
lean_dec_ref(v_expr_2535_);
v___x_2654_ = lean_box(2);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2654_);
v___x_2656_ = v___x_2563_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec_ref_known(v___x_2551_, 2);
lean_dec(v_a_2543_);
lean_dec_ref(v_expectedType_2536_);
lean_dec_ref(v_expr_2535_);
v_a_2659_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2560_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2560_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_a_2545_);
lean_dec(v_a_2543_);
lean_dec_ref(v_expectedType_2536_);
lean_dec_ref(v_expr_2535_);
v_a_2667_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2546_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2546_);
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
lean_dec(v_a_2543_);
lean_dec_ref(v_expectedType_2536_);
lean_dec_ref(v_expr_2535_);
v_a_2675_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2544_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2544_);
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
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec_ref(v_expectedType_2536_);
lean_dec_ref(v_expr_2535_);
v_a_2683_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2542_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2542_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2691_, lean_object* v_expectedType_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2691_, v_expectedType_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2699_, lean_object* v_msg_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2707_, lean_object* v_msg_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2707_, v_msg_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2715_, lean_object* v_expectedType_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2715_, v_expectedType_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2747_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2747_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2747_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
switch(lean_obj_tag(v_a_2723_))
{
case 0:
{
lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2727_ = lean_box(0);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2727_);
v___x_2729_ = v___x_2725_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
case 1:
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2742_; 
v_a_2731_ = lean_ctor_get(v_a_2723_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_a_2723_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2733_ = v_a_2723_;
v_isShared_2734_ = v_isSharedCheck_2742_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v_a_2723_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2742_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_fst_2735_; lean_object* v___x_2737_; 
v_fst_2735_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_fst_2735_);
lean_dec(v_a_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v_fst_2735_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_fst_2735_);
v___x_2737_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2739_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2737_);
v___x_2739_ = v___x_2725_;
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
default: 
{
lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2743_ = lean_box(2);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2743_);
v___x_2745_ = v___x_2725_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v_a_2748_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2722_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2722_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2756_, lean_object* v_expectedType_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2756_, v_expectedType_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
return v_res_2763_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2775_ = l_Lean_stringToMessageData(v___x_2774_);
return v___x_2775_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2778_ = l_Lean_stringToMessageData(v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v___x_2785_; 
lean_inc(v_a_2783_);
lean_inc_ref(v_a_2782_);
lean_inc(v_a_2781_);
lean_inc_ref(v_a_2780_);
lean_inc_ref(v_expr_2779_);
v___x_2785_ = lean_infer_type(v_expr_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc_n(v_a_2786_, 2);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2787_ = l_Lean_Meta_getLevel(v_a_2786_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2789_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc_n(v_a_2790_, 2);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = l_Lean_mkSort(v_a_2790_);
lean_inc(v_a_2786_);
v___x_2792_ = l_Lean_mkArrow(v_a_2786_, v___x_2791_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v___x_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2794_, 0, v_a_2793_);
v___x_2795_ = 0;
v___x_2796_ = lean_box(0);
v___x_2797_ = l_Lean_Meta_mkFreshExprMVar(v___x_2794_, v___x_2795_, v___x_2796_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc_n(v_a_2798_, 2);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2800_ = lean_box(0);
v___x_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2801_, 0, v_a_2790_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2802_, 0, v_a_2788_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
lean_inc_ref(v___x_2802_);
v___x_2803_ = l_Lean_Expr_const___override(v___x_2799_, v___x_2802_);
lean_inc(v_a_2786_);
v___x_2804_ = l_Lean_mkAppB(v___x_2803_, v_a_2786_, v_a_2798_);
v___x_2805_ = lean_box(0);
v___x_2806_ = l_Lean_Meta_trySynthInstance(v___x_2804_, v___x_2805_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2893_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2893_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2893_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
if (lean_obj_tag(v_a_2807_) == 1)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2889_; 
lean_del_object(v___x_2809_);
v_a_2811_ = lean_ctor_get(v_a_2807_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_a_2807_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2813_ = v_a_2807_;
v_isShared_2814_ = v_isSharedCheck_2889_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v_a_2807_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2889_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2815_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2816_ = l_Lean_Expr_const___override(v___x_2815_, v___x_2802_);
lean_inc_ref(v_expr_2779_);
lean_inc(v_a_2811_);
v___x_2817_ = l_Lean_mkApp4(v___x_2816_, v_a_2786_, v_a_2798_, v_a_2811_, v_expr_2779_);
v___x_2818_ = l_Lean_Meta_expandCoe(v___x_2817_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2880_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2880_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2880_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_fst_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2878_; 
v_fst_2823_ = lean_ctor_get(v_a_2819_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; 
v_unused_2879_ = lean_ctor_get(v_a_2819_, 1);
lean_dec(v_unused_2879_);
v___x_2825_ = v_a_2819_;
v_isShared_2826_ = v_isSharedCheck_2878_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_fst_2823_);
lean_dec(v_a_2819_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2878_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2834_; 
lean_inc(v_a_2783_);
lean_inc_ref(v_a_2782_);
lean_inc(v_a_2781_);
lean_inc_ref(v_a_2780_);
lean_inc(v_fst_2823_);
v___x_2834_ = lean_infer_type(v_fst_2823_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
lean_inc(v_a_2783_);
lean_inc_ref(v_a_2782_);
lean_inc(v_a_2781_);
lean_inc_ref(v_a_2780_);
v___x_2836_ = lean_whnf(v_a_2835_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; uint8_t v___x_2838_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2838_ = l_Lean_Expr_isForall(v_a_2837_);
lean_dec(v_a_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
lean_del_object(v___x_2821_);
lean_del_object(v___x_2813_);
v___x_2839_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2840_ = l_Lean_indentExpr(v_expr_2779_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set_tag(v___x_2825_, 7);
lean_ctor_set(v___x_2825_, 1, v___x_2840_);
lean_ctor_set(v___x_2825_, 0, v___x_2839_);
v___x_2842_ = v___x_2825_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
v___x_2843_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2842_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = l_Lean_indentExpr(v_fst_2823_);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2848_ = l_Lean_indentExpr(v_a_2811_);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = l_Lean_MessageData_hint_x27(v___x_2849_);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2846_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2851_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
else
{
lean_del_object(v___x_2825_);
lean_dec(v_a_2811_);
lean_dec_ref(v_expr_2779_);
goto v___jp_2827_;
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_del_object(v___x_2825_);
lean_dec(v_fst_2823_);
lean_del_object(v___x_2821_);
lean_del_object(v___x_2813_);
lean_dec(v_a_2811_);
lean_dec_ref(v_expr_2779_);
v_a_2862_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2836_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2836_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_del_object(v___x_2825_);
lean_dec(v_fst_2823_);
lean_del_object(v___x_2821_);
lean_del_object(v___x_2813_);
lean_dec(v_a_2811_);
lean_dec_ref(v_expr_2779_);
v_a_2870_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2834_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2834_);
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
v___jp_2827_:
{
lean_object* v___x_2829_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v_fst_2823_);
v___x_2829_ = v___x_2813_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_fst_2823_);
v___x_2829_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2831_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2829_);
v___x_2831_ = v___x_2821_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_del_object(v___x_2813_);
lean_dec(v_a_2811_);
lean_dec_ref(v_expr_2779_);
v_a_2881_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2818_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2818_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
else
{
lean_object* v___x_2891_; 
lean_dec(v_a_2807_);
lean_dec_ref_known(v___x_2802_, 2);
lean_dec(v_a_2798_);
lean_dec(v_a_2786_);
lean_dec_ref(v_expr_2779_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2805_);
v___x_2891_ = v___x_2809_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2805_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec_ref_known(v___x_2802_, 2);
lean_dec(v_a_2798_);
lean_dec(v_a_2786_);
lean_dec_ref(v_expr_2779_);
v_a_2894_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2806_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2806_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_a_2790_);
lean_dec(v_a_2788_);
lean_dec(v_a_2786_);
lean_dec_ref(v_expr_2779_);
v_a_2902_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2797_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2797_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v_a_2790_);
lean_dec(v_a_2788_);
lean_dec(v_a_2786_);
lean_dec_ref(v_expr_2779_);
v_a_2910_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2792_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2792_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_a_2788_);
lean_dec(v_a_2786_);
lean_dec_ref(v_expr_2779_);
v_a_2918_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2789_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2789_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_a_2786_);
lean_dec_ref(v_expr_2779_);
v_a_2926_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2787_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2787_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v_expr_2779_);
v_a_2934_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2785_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2785_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
return v_res_2948_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2957_ = l_Lean_stringToMessageData(v___x_2956_);
return v___x_2957_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2960_ = l_Lean_stringToMessageData(v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v___x_2967_; 
lean_inc(v_a_2965_);
lean_inc_ref(v_a_2964_);
lean_inc(v_a_2963_);
lean_inc_ref(v_a_2962_);
lean_inc_ref(v_expr_2961_);
v___x_2967_ = lean_infer_type(v_expr_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc_n(v_a_2968_, 2);
lean_dec_ref_known(v___x_2967_, 1);
v___x_2969_ = l_Lean_Meta_getLevel(v_a_2968_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2971_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc_n(v_a_2972_, 2);
lean_dec_ref_known(v___x_2971_, 1);
v___x_2973_ = l_Lean_mkSort(v_a_2972_);
v___x_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
v___x_2975_ = 0;
v___x_2976_ = lean_box(0);
v___x_2977_ = l_Lean_Meta_mkFreshExprMVar(v___x_2974_, v___x_2975_, v___x_2976_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc_n(v_a_2978_, 2);
lean_dec_ref_known(v___x_2977_, 1);
v___x_2979_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2981_, 0, v_a_2972_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
v___x_2982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_a_2970_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
lean_inc_ref(v___x_2982_);
v___x_2983_ = l_Lean_Expr_const___override(v___x_2979_, v___x_2982_);
lean_inc(v_a_2968_);
v___x_2984_ = l_Lean_mkAppB(v___x_2983_, v_a_2968_, v_a_2978_);
v___x_2985_ = lean_box(0);
v___x_2986_ = l_Lean_Meta_trySynthInstance(v___x_2984_, v___x_2985_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3073_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_3073_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3073_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
if (lean_obj_tag(v_a_2987_) == 1)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3069_; 
lean_del_object(v___x_2989_);
v_a_2991_ = lean_ctor_get(v_a_2987_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_a_2987_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_2993_ = v_a_2987_;
v_isShared_2994_ = v_isSharedCheck_3069_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v_a_2987_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3069_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2995_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_2996_ = l_Lean_Expr_const___override(v___x_2995_, v___x_2982_);
lean_inc_ref(v_expr_2961_);
lean_inc(v_a_2991_);
v___x_2997_ = l_Lean_mkApp4(v___x_2996_, v_a_2968_, v_a_2978_, v_a_2991_, v_expr_2961_);
v___x_2998_ = l_Lean_Meta_expandCoe(v___x_2997_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3060_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3060_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3060_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v_fst_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3058_; 
v_fst_3003_ = lean_ctor_get(v_a_2999_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_a_2999_);
if (v_isSharedCheck_3058_ == 0)
{
lean_object* v_unused_3059_; 
v_unused_3059_ = lean_ctor_get(v_a_2999_, 1);
lean_dec(v_unused_3059_);
v___x_3005_ = v_a_2999_;
v_isShared_3006_ = v_isSharedCheck_3058_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_fst_3003_);
lean_dec(v_a_2999_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3058_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3014_; 
lean_inc(v_a_2965_);
lean_inc_ref(v_a_2964_);
lean_inc(v_a_2963_);
lean_inc_ref(v_a_2962_);
lean_inc(v_fst_3003_);
v___x_3014_ = lean_infer_type(v_fst_3003_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
lean_inc(v_a_2965_);
lean_inc_ref(v_a_2964_);
lean_inc(v_a_2963_);
lean_inc_ref(v_a_2962_);
v___x_3016_ = lean_whnf(v_a_3015_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; uint8_t v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = l_Lean_Expr_isSort(v_a_3017_);
lean_dec(v_a_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3022_; 
lean_del_object(v___x_3001_);
lean_del_object(v___x_2993_);
v___x_3019_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3020_ = l_Lean_indentExpr(v_expr_2961_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set_tag(v___x_3005_, 7);
lean_ctor_set(v___x_3005_, 1, v___x_3020_);
lean_ctor_set(v___x_3005_, 0, v___x_3019_);
v___x_3022_ = v___x_3005_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
v___x_3023_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = l_Lean_indentExpr(v_fst_3003_);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3028_ = l_Lean_indentExpr(v_a_2991_);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = l_Lean_MessageData_hint_x27(v___x_3029_);
v___x_3031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3026_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3031_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3032_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3032_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
else
{
lean_del_object(v___x_3005_);
lean_dec(v_a_2991_);
lean_dec_ref(v_expr_2961_);
goto v___jp_3007_;
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_del_object(v___x_3005_);
lean_dec(v_fst_3003_);
lean_del_object(v___x_3001_);
lean_del_object(v___x_2993_);
lean_dec(v_a_2991_);
lean_dec_ref(v_expr_2961_);
v_a_3042_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3016_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3016_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_del_object(v___x_3005_);
lean_dec(v_fst_3003_);
lean_del_object(v___x_3001_);
lean_del_object(v___x_2993_);
lean_dec(v_a_2991_);
lean_dec_ref(v_expr_2961_);
v_a_3050_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3014_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3014_);
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
v___jp_3007_:
{
lean_object* v___x_3009_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v_fst_3003_);
v___x_3009_ = v___x_2993_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_fst_3003_);
v___x_3009_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3011_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3009_);
v___x_3011_ = v___x_3001_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_del_object(v___x_2993_);
lean_dec(v_a_2991_);
lean_dec_ref(v_expr_2961_);
v_a_3061_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_2998_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_2998_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
else
{
lean_object* v___x_3071_; 
lean_dec(v_a_2987_);
lean_dec_ref_known(v___x_2982_, 2);
lean_dec(v_a_2978_);
lean_dec(v_a_2968_);
lean_dec_ref(v_expr_2961_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2985_);
v___x_3071_ = v___x_2989_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_2985_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec_ref_known(v___x_2982_, 2);
lean_dec(v_a_2978_);
lean_dec(v_a_2968_);
lean_dec_ref(v_expr_2961_);
v_a_3074_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_2986_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_2986_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v_a_2972_);
lean_dec(v_a_2970_);
lean_dec(v_a_2968_);
lean_dec_ref(v_expr_2961_);
v_a_3082_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_2977_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_2977_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v_a_2970_);
lean_dec(v_a_2968_);
lean_dec_ref(v_expr_2961_);
v_a_3090_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_2971_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_2971_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_a_2968_);
lean_dec_ref(v_expr_2961_);
v_a_3098_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_2969_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_2969_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v_expr_2961_);
v_a_3106_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_2967_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_2967_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_);
lean_dec(v_a_3118_);
lean_dec_ref(v_a_3117_);
lean_dec(v_a_3116_);
lean_dec_ref(v_a_3115_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3121_, lean_object* v___y_3122_){
_start:
{
uint8_t v___x_3124_; 
v___x_3124_ = l_Lean_Expr_hasMVar(v_e_3121_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_e_3121_);
return v___x_3125_;
}
else
{
lean_object* v___x_3126_; lean_object* v_mctx_3127_; lean_object* v___x_3128_; lean_object* v_fst_3129_; lean_object* v_snd_3130_; lean_object* v___x_3131_; lean_object* v_cache_3132_; lean_object* v_zetaDeltaFVarIds_3133_; lean_object* v_postponed_3134_; lean_object* v_diag_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3144_; 
v___x_3126_ = lean_st_ref_get(v___y_3122_);
v_mctx_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc_ref(v_mctx_3127_);
lean_dec(v___x_3126_);
v___x_3128_ = l_Lean_instantiateMVarsCore(v_mctx_3127_, v_e_3121_);
v_fst_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_fst_3129_);
v_snd_3130_ = lean_ctor_get(v___x_3128_, 1);
lean_inc(v_snd_3130_);
lean_dec_ref(v___x_3128_);
v___x_3131_ = lean_st_ref_take(v___y_3122_);
v_cache_3132_ = lean_ctor_get(v___x_3131_, 1);
v_zetaDeltaFVarIds_3133_ = lean_ctor_get(v___x_3131_, 2);
v_postponed_3134_ = lean_ctor_get(v___x_3131_, 3);
v_diag_3135_ = lean_ctor_get(v___x_3131_, 4);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3144_ == 0)
{
lean_object* v_unused_3145_; 
v_unused_3145_ = lean_ctor_get(v___x_3131_, 0);
lean_dec(v_unused_3145_);
v___x_3137_ = v___x_3131_;
v_isShared_3138_ = v_isSharedCheck_3144_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_diag_3135_);
lean_inc(v_postponed_3134_);
lean_inc(v_zetaDeltaFVarIds_3133_);
lean_inc(v_cache_3132_);
lean_dec(v___x_3131_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3144_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v_snd_3130_);
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_snd_3130_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_cache_3132_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_zetaDeltaFVarIds_3133_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_postponed_3134_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_diag_3135_);
v___x_3140_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = lean_st_ref_put(v___y_3122_, v___x_3140_);
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_fst_3129_);
return v___x_3142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3146_, v___y_3147_);
lean_dec(v___y_3147_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3150_, v___y_3152_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v___y_3171_; lean_object* v___x_3210_; uint8_t v_transparency_3211_; uint8_t v___x_3212_; uint8_t v___x_3213_; 
v___x_3210_ = l_Lean_Meta_Context_config(v_a_3165_);
v_transparency_3211_ = lean_ctor_get_uint8(v___x_3210_, 9);
lean_dec_ref(v___x_3210_);
v___x_3212_ = 2;
v___x_3213_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v_keyedConfig_3214_; uint8_t v_trackZetaDelta_3215_; lean_object* v_zetaDeltaSet_3216_; lean_object* v_lctx_3217_; lean_object* v_localInstances_3218_; lean_object* v_defEqCtx_x3f_3219_; lean_object* v_synthPendingDepth_3220_; lean_object* v_customCanUnfoldPredicate_x3f_3221_; uint8_t v_univApprox_3222_; uint8_t v_inTypeClassResolution_3223_; uint8_t v_cacheInferType_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v_keyedConfig_3214_ = lean_ctor_get(v_a_3165_, 0);
v_trackZetaDelta_3215_ = lean_ctor_get_uint8(v_a_3165_, sizeof(void*)*7);
v_zetaDeltaSet_3216_ = lean_ctor_get(v_a_3165_, 1);
v_lctx_3217_ = lean_ctor_get(v_a_3165_, 2);
v_localInstances_3218_ = lean_ctor_get(v_a_3165_, 3);
v_defEqCtx_x3f_3219_ = lean_ctor_get(v_a_3165_, 4);
v_synthPendingDepth_3220_ = lean_ctor_get(v_a_3165_, 5);
v_customCanUnfoldPredicate_x3f_3221_ = lean_ctor_get(v_a_3165_, 6);
v_univApprox_3222_ = lean_ctor_get_uint8(v_a_3165_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3223_ = lean_ctor_get_uint8(v_a_3165_, sizeof(void*)*7 + 2);
v_cacheInferType_3224_ = lean_ctor_get_uint8(v_a_3165_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3214_);
v___x_3225_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3212_, v_keyedConfig_3214_);
lean_inc(v_customCanUnfoldPredicate_x3f_3221_);
lean_inc(v_synthPendingDepth_3220_);
lean_inc(v_defEqCtx_x3f_3219_);
lean_inc_ref(v_localInstances_3218_);
lean_inc_ref(v_lctx_3217_);
lean_inc(v_zetaDeltaSet_3216_);
v___x_3226_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
lean_ctor_set(v___x_3226_, 1, v_zetaDeltaSet_3216_);
lean_ctor_set(v___x_3226_, 2, v_lctx_3217_);
lean_ctor_set(v___x_3226_, 3, v_localInstances_3218_);
lean_ctor_set(v___x_3226_, 4, v_defEqCtx_x3f_3219_);
lean_ctor_set(v___x_3226_, 5, v_synthPendingDepth_3220_);
lean_ctor_set(v___x_3226_, 6, v_customCanUnfoldPredicate_x3f_3221_);
lean_ctor_set_uint8(v___x_3226_, sizeof(void*)*7, v_trackZetaDelta_3215_);
lean_ctor_set_uint8(v___x_3226_, sizeof(void*)*7 + 1, v_univApprox_3222_);
lean_ctor_set_uint8(v___x_3226_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3223_);
lean_ctor_set_uint8(v___x_3226_, sizeof(void*)*7 + 3, v_cacheInferType_3224_);
lean_inc(v_a_3168_);
lean_inc_ref(v_a_3167_);
lean_inc(v_a_3166_);
v___x_3227_ = lean_whnf(v_type_3164_, v___x_3226_, v_a_3166_, v_a_3167_, v_a_3168_);
v___y_3171_ = v___x_3227_;
goto v___jp_3170_;
}
else
{
lean_object* v___x_3228_; 
lean_inc(v_a_3168_);
lean_inc_ref(v_a_3167_);
lean_inc(v_a_3166_);
lean_inc_ref(v_a_3165_);
v___x_3228_ = lean_whnf(v_type_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_);
v___y_3171_ = v___x_3228_;
goto v___jp_3170_;
}
v___jp_3170_:
{
if (lean_obj_tag(v___y_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3201_; 
v_a_3172_ = lean_ctor_get(v___y_3171_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___y_3171_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3174_ = v___y_3171_;
v_isShared_3175_ = v_isSharedCheck_3201_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___y_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3201_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
if (lean_obj_tag(v_a_3172_) == 5)
{
lean_object* v_fn_3176_; lean_object* v_arg_3177_; lean_object* v___x_3178_; lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3196_; 
lean_del_object(v___x_3174_);
v_fn_3176_ = lean_ctor_get(v_a_3172_, 0);
lean_inc_ref(v_fn_3176_);
v_arg_3177_ = lean_ctor_get(v_a_3172_, 1);
lean_inc_ref(v_arg_3177_);
lean_dec_ref_known(v_a_3172_, 2);
v___x_3178_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3176_, v_a_3166_);
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3196_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3196_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3195_; 
v___x_3183_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3177_, v_a_3166_);
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3186_ = v___x_3183_;
v_isShared_3187_ = v_isSharedCheck_3195_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3195_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_a_3179_);
lean_ctor_set(v___x_3188_, 1, v_a_3184_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set_tag(v___x_3181_, 1);
lean_ctor_set(v___x_3181_, 0, v___x_3188_);
v___x_3190_ = v___x_3181_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3192_; 
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v___x_3190_);
v___x_3192_ = v___x_3186_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
}
else
{
lean_object* v___x_3197_; lean_object* v___x_3199_; 
lean_dec(v_a_3172_);
v___x_3197_ = lean_box(0);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3197_);
v___x_3199_ = v___x_3174_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
v_a_3202_ = lean_ctor_get(v___y_3171_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___y_3171_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___y_3171_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___y_3171_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l_Lean_Meta_isTypeApp_x3f(v_type_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_Meta_isTypeApp_x3f(v_type_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3278_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3278_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3278_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
if (lean_obj_tag(v_a_3243_) == 1)
{
lean_object* v_val_3247_; lean_object* v_fst_3248_; lean_object* v___x_3249_; 
lean_del_object(v___x_3245_);
v_val_3247_ = lean_ctor_get(v_a_3243_, 0);
lean_inc(v_val_3247_);
lean_dec_ref_known(v_a_3243_, 1);
v_fst_3248_ = lean_ctor_get(v_val_3247_, 0);
lean_inc(v_fst_3248_);
lean_dec(v_val_3247_);
v___x_3249_ = l_Lean_Meta_isMonad_x3f(v_fst_3248_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3264_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3264_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3264_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
if (lean_obj_tag(v_a_3250_) == 0)
{
uint8_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3254_ = 0;
v___x_3255_ = lean_box(v___x_3254_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3255_);
v___x_3257_ = v___x_3252_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
else
{
uint8_t v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
lean_dec_ref_known(v_a_3250_, 1);
v___x_3259_ = 1;
v___x_3260_ = lean_box(v___x_3259_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3260_);
v___x_3262_ = v___x_3252_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
v_a_3265_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3249_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3249_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
uint8_t v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_dec(v_a_3243_);
v___x_3273_ = 0;
v___x_3274_ = lean_box(v___x_3273_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3274_);
v___x_3276_ = v___x_3245_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
v_a_3279_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3242_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3242_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_Meta_isMonadApp(v_type_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
return v_res_3293_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3294_, lean_object* v_opt_3295_){
_start:
{
lean_object* v_name_3296_; lean_object* v_defValue_3297_; lean_object* v_map_3298_; lean_object* v___x_3299_; 
v_name_3296_ = lean_ctor_get(v_opt_3295_, 0);
v_defValue_3297_ = lean_ctor_get(v_opt_3295_, 1);
v_map_3298_ = lean_ctor_get(v_opts_3294_, 0);
v___x_3299_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3298_, v_name_3296_);
if (lean_obj_tag(v___x_3299_) == 0)
{
uint8_t v___x_3300_; 
v___x_3300_ = lean_unbox(v_defValue_3297_);
return v___x_3300_;
}
else
{
lean_object* v_val_3301_; 
v_val_3301_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_val_3301_);
lean_dec_ref_known(v___x_3299_, 1);
if (lean_obj_tag(v_val_3301_) == 1)
{
uint8_t v_v_3302_; 
v_v_3302_ = lean_ctor_get_uint8(v_val_3301_, 0);
lean_dec_ref_known(v_val_3301_, 0);
return v_v_3302_;
}
else
{
uint8_t v___x_3303_; 
lean_dec(v_val_3301_);
v___x_3303_ = lean_unbox(v_defValue_3297_);
return v___x_3303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3304_, lean_object* v_opt_3305_){
_start:
{
uint8_t v_res_3306_; lean_object* v_r_3307_; 
v_res_3306_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3304_, v_opt_3305_);
lean_dec_ref(v_opt_3305_);
lean_dec_ref(v_opts_3304_);
v_r_3307_ = lean_box(v_res_3306_);
return v_r_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v_x_3318_);
return v_res_3324_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = lean_unsigned_to_nat(0u);
v___x_3335_ = l_Lean_mkBVar(v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3347_, lean_object* v_expectedType_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v_a_3355_; lean_object* v___y_3363_; lean_object* v___x_3373_; lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3777_; 
v___x_3373_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3348_, v_a_3350_);
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3777_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3777_;
goto v_resetjp_3375_;
}
v___jp_3354_:
{
uint8_t v___x_3356_; 
v___x_3356_ = l_Lean_Exception_isInterrupt(v_a_3355_);
if (v___x_3356_ == 0)
{
uint8_t v___x_3357_; 
lean_inc_ref(v_a_3355_);
v___x_3357_ = l_Lean_Exception_isRuntime(v_a_3355_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
lean_dec_ref(v_a_3355_);
v___x_3358_ = lean_box(0);
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
return v___x_3359_;
}
else
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v_a_3355_);
return v___x_3360_;
}
}
else
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3361_, 0, v_a_3355_);
return v___x_3361_;
}
}
v___jp_3362_:
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3372_; 
v_a_3364_ = lean_ctor_get(v___y_3363_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___y_3363_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3366_ = v___y_3363_;
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___y_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_a_3368_; lean_object* v___x_3370_; 
v_a_3368_ = lean_ctor_get(v_a_3364_, 0);
lean_inc(v_a_3368_);
lean_dec(v_a_3364_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v_a_3368_);
v___x_3370_ = v___x_3366_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; 
lean_inc(v_a_3352_);
lean_inc_ref(v_a_3351_);
lean_inc(v_a_3350_);
lean_inc_ref(v_a_3349_);
lean_inc_ref(v_e_3347_);
v___x_3378_ = lean_infer_type(v_e_3347_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3768_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
v___x_3380_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3379_, v_a_3350_);
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3768_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3768_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3385_; 
lean_inc(v_a_3374_);
v___x_3385_ = l_Lean_Meta_isTypeApp_x3f(v_a_3374_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3759_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3759_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3759_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
if (lean_obj_tag(v_a_3386_) == 1)
{
lean_object* v_val_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3754_; 
lean_del_object(v___x_3388_);
v_val_3390_ = lean_ctor_get(v_a_3386_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_a_3386_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3392_ = v_a_3386_;
v_isShared_3393_ = v_isSharedCheck_3754_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_val_3390_);
lean_dec(v_a_3386_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3754_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v_fst_3394_; lean_object* v_snd_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3753_; 
v_fst_3394_ = lean_ctor_get(v_val_3390_, 0);
v_snd_3395_ = lean_ctor_get(v_val_3390_, 1);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_val_3390_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3397_ = v_val_3390_;
v_isShared_3398_ = v_isSharedCheck_3753_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_snd_3395_);
lean_inc(v_fst_3394_);
lean_dec(v_val_3390_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3753_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; 
lean_inc(v_a_3381_);
v___x_3399_ = l_Lean_Meta_isTypeApp_x3f(v_a_3381_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3744_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3744_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3744_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
if (lean_obj_tag(v_a_3400_) == 1)
{
lean_object* v_val_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3739_; 
lean_del_object(v___x_3402_);
v_val_3404_ = lean_ctor_get(v_a_3400_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v_a_3400_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3406_ = v_a_3400_;
v_isShared_3407_ = v_isSharedCheck_3739_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_val_3404_);
lean_dec(v_a_3400_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3739_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v_fst_3408_; lean_object* v_snd_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3738_; 
v_fst_3408_ = lean_ctor_get(v_val_3404_, 0);
v_snd_3409_ = lean_ctor_get(v_val_3404_, 1);
v_isSharedCheck_3738_ = !lean_is_exclusive(v_val_3404_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3411_ = v_val_3404_;
v_isShared_3412_ = v_isSharedCheck_3738_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_snd_3409_);
lean_inc(v_fst_3408_);
lean_dec(v_val_3404_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3738_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Meta_saveState___redArg(v_a_3350_, v_a_3352_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3415_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
lean_inc(v_fst_3394_);
lean_inc(v_fst_3408_);
v___x_3415_ = l_Lean_Meta_isExprDefEq(v_fst_3408_, v_fst_3394_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3721_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3721_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3721_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_unbox(v_a_3416_);
lean_dec(v_a_3416_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; uint8_t v___x_3423_; 
lean_dec(v_a_3414_);
lean_del_object(v___x_3392_);
lean_del_object(v___x_3383_);
lean_del_object(v___x_3376_);
v___x_3421_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3351_);
v___x_3422_ = l_Lean_Meta_autoLift;
v___x_3423_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v___x_3421_, v___x_3422_);
lean_dec_ref(v___x_3421_);
if (v___x_3423_ == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3426_; 
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v___x_3424_ = lean_box(0);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3424_);
v___x_3426_ = v___x_3418_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
else
{
lean_object* v___x_3428_; 
lean_del_object(v___x_3418_);
lean_inc(v_a_3352_);
lean_inc_ref(v_a_3351_);
lean_inc(v_a_3350_);
lean_inc_ref(v_a_3349_);
lean_inc(v_fst_3408_);
v___x_3428_ = lean_infer_type(v_fst_3408_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3430_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3428_, 1);
lean_inc(v_a_3352_);
lean_inc_ref(v_a_3351_);
lean_inc(v_a_3350_);
lean_inc_ref(v_a_3349_);
v___x_3430_ = lean_whnf(v_a_3429_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
if (lean_obj_tag(v_a_3431_) == 7)
{
lean_object* v_binderType_3432_; 
v_binderType_3432_ = lean_ctor_get(v_a_3431_, 1);
if (lean_obj_tag(v_binderType_3432_) == 3)
{
lean_object* v_body_3433_; 
v_body_3433_ = lean_ctor_get(v_a_3431_, 2);
if (lean_obj_tag(v_body_3433_) == 3)
{
lean_object* v_u_3434_; lean_object* v_u_3435_; lean_object* v___x_3436_; 
lean_inc_ref(v_body_3433_);
lean_inc_ref(v_binderType_3432_);
lean_dec_ref_known(v_a_3431_, 3);
v_u_3434_ = lean_ctor_get(v_binderType_3432_, 0);
lean_inc(v_u_3434_);
lean_dec_ref_known(v_binderType_3432_, 1);
v_u_3435_ = lean_ctor_get(v_body_3433_, 0);
lean_inc(v_u_3435_);
lean_dec_ref_known(v_body_3433_, 1);
lean_inc(v_a_3352_);
lean_inc_ref(v_a_3351_);
lean_inc(v_a_3350_);
lean_inc_ref(v_a_3349_);
lean_inc(v_fst_3394_);
v___x_3436_ = lean_infer_type(v_fst_3394_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3438_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3436_, 1);
lean_inc(v_a_3352_);
lean_inc_ref(v_a_3351_);
lean_inc(v_a_3350_);
lean_inc_ref(v_a_3349_);
v___x_3438_ = lean_whnf(v_a_3437_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
if (lean_obj_tag(v_a_3439_) == 7)
{
lean_object* v_binderType_3440_; 
v_binderType_3440_ = lean_ctor_get(v_a_3439_, 1);
if (lean_obj_tag(v_binderType_3440_) == 3)
{
lean_object* v_body_3441_; 
v_body_3441_ = lean_ctor_get(v_a_3439_, 2);
if (lean_obj_tag(v_body_3441_) == 3)
{
lean_object* v_u_3442_; lean_object* v_u_3443_; lean_object* v___x_3444_; 
lean_inc_ref(v_body_3441_);
lean_inc_ref(v_binderType_3440_);
lean_dec_ref_known(v_a_3439_, 3);
v_u_3442_ = lean_ctor_get(v_binderType_3440_, 0);
lean_inc(v_u_3442_);
lean_dec_ref_known(v_binderType_3440_, 1);
v_u_3443_ = lean_ctor_get(v_body_3441_, 0);
lean_inc(v_u_3443_);
lean_dec_ref_known(v_body_3441_, 1);
v___x_3444_ = l_Lean_Meta_decLevel(v_u_3434_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref_known(v___x_3444_, 1);
v___x_3446_ = l_Lean_Meta_decLevel(v_u_3442_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
lean_inc(v_a_3445_);
v___x_3448_ = l_Lean_Meta_isLevelDefEq(v_a_3445_, v_a_3447_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3613_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3613_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3613_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
uint8_t v___x_3453_; 
v___x_3453_ = lean_unbox(v_a_3449_);
lean_dec(v_a_3449_);
if (v___x_3453_ == 1)
{
lean_object* v___x_3454_; 
lean_del_object(v___x_3451_);
v___x_3454_ = l_Lean_Meta_decLevel(v_u_3435_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3456_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v___x_3456_ = l_Lean_Meta_decLevel(v_u_3443_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3459_ = lean_box(0);
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 1);
lean_ctor_set(v___x_3411_, 1, v___x_3459_);
lean_ctor_set(v___x_3411_, 0, v_a_3457_);
v___x_3461_ = v___x_3411_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3457_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3463_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 1);
lean_ctor_set(v___x_3397_, 1, v___x_3461_);
lean_ctor_set(v___x_3397_, 0, v_a_3455_);
v___x_3463_ = v___x_3397_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3455_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3464_, 0, v_a_3445_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = l_Lean_Expr_const___override(v___x_3458_, v___x_3464_);
v___x_3466_ = lean_unsigned_to_nat(2u);
v___x_3467_ = lean_mk_empty_array_with_capacity(v___x_3466_);
lean_inc(v_fst_3408_);
v___x_3468_ = lean_array_push(v___x_3467_, v_fst_3408_);
lean_inc(v_fst_3394_);
v___x_3469_ = lean_array_push(v___x_3468_, v_fst_3394_);
v___x_3470_ = l_Lean_mkAppN(v___x_3465_, v___x_3469_);
lean_dec_ref(v___x_3469_);
v___x_3471_ = lean_box(0);
v___x_3472_ = l_Lean_Meta_trySynthInstance(v___x_3470_, v___x_3471_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3603_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3603_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3603_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
if (lean_obj_tag(v_a_3473_) == 1)
{
lean_object* v_a_3477_; lean_object* v___x_3478_; 
lean_del_object(v___x_3475_);
v_a_3477_ = lean_ctor_get(v_a_3473_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v_a_3473_, 1);
lean_inc(v_snd_3409_);
v___x_3478_ = l_Lean_Meta_getDecLevel(v_snd_3409_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3480_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___x_3480_ = l_Lean_Meta_getDecLevel(v_a_3381_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3482_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v___x_3480_, 1);
lean_inc(v_a_3374_);
v___x_3482_ = l_Lean_Meta_getDecLevel(v_a_3374_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref_known(v___x_3482_, 1);
v___x_3484_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3485_, 0, v_a_3483_);
lean_ctor_set(v___x_3485_, 1, v___x_3459_);
v___x_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3486_, 0, v_a_3481_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3487_, 0, v_a_3479_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
lean_inc_ref(v___x_3487_);
v___x_3488_ = l_Lean_mkConst(v___x_3484_, v___x_3487_);
v___x_3489_ = lean_unsigned_to_nat(5u);
v___x_3490_ = lean_mk_empty_array_with_capacity(v___x_3489_);
lean_inc(v_fst_3408_);
v___x_3491_ = lean_array_push(v___x_3490_, v_fst_3408_);
lean_inc(v_fst_3394_);
v___x_3492_ = lean_array_push(v___x_3491_, v_fst_3394_);
lean_inc(v_a_3477_);
v___x_3493_ = lean_array_push(v___x_3492_, v_a_3477_);
lean_inc(v_snd_3409_);
v___x_3494_ = lean_array_push(v___x_3493_, v_snd_3409_);
lean_inc_ref(v_e_3347_);
v___x_3495_ = lean_array_push(v___x_3494_, v_e_3347_);
v___x_3496_ = l_Lean_mkAppN(v___x_3488_, v___x_3495_);
lean_dec_ref(v___x_3495_);
lean_inc(v_a_3352_);
lean_inc_ref(v_a_3351_);
lean_inc(v_a_3350_);
lean_inc_ref(v_a_3349_);
lean_inc_ref(v___x_3496_);
v___x_3497_ = lean_infer_type(v___x_3496_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
lean_inc(v_a_3374_);
v___x_3499_ = l_Lean_Meta_isExprDefEq(v_a_3374_, v_a_3498_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3594_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3594_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3594_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
uint8_t v___x_3504_; 
v___x_3504_ = lean_unbox(v_a_3500_);
lean_dec(v_a_3500_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
lean_del_object(v___x_3502_);
lean_dec_ref(v___x_3496_);
lean_del_object(v___x_3406_);
lean_inc(v_fst_3394_);
v___x_3505_ = l_Lean_Meta_isMonad_x3f(v_fst_3394_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3586_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3508_ = v___x_3505_;
v_isShared_3509_ = v_isSharedCheck_3586_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3586_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
if (lean_obj_tag(v_a_3506_) == 1)
{
lean_object* v_val_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3582_; 
lean_del_object(v___x_3508_);
v_val_3510_ = lean_ctor_get(v_a_3506_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_a_3506_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3512_ = v_a_3506_;
v_isShared_3513_ = v_isSharedCheck_3582_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_val_3510_);
lean_dec(v_a_3506_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3582_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; 
lean_inc(v_snd_3409_);
v___x_3514_ = l_Lean_Meta_getLevel(v_snd_3409_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3516_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
lean_inc(v_snd_3395_);
v___x_3516_ = l_Lean_Meta_getLevel(v_snd_3395_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3516_, 1);
v___x_3518_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3519_ = 0;
v___x_3520_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3521_, 0, v_a_3517_);
lean_ctor_set(v___x_3521_, 1, v___x_3459_);
v___x_3522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_a_3515_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l_Lean_mkConst(v___x_3520_, v___x_3522_);
v___x_3524_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3525_ = lean_unsigned_to_nat(3u);
v___x_3526_ = lean_mk_empty_array_with_capacity(v___x_3525_);
lean_inc_n(v_snd_3409_, 2);
v___x_3527_ = lean_array_push(v___x_3526_, v_snd_3409_);
v___x_3528_ = lean_array_push(v___x_3527_, v___x_3524_);
lean_inc(v_snd_3395_);
v___x_3529_ = lean_array_push(v___x_3528_, v_snd_3395_);
v___x_3530_ = l_Lean_mkAppN(v___x_3523_, v___x_3529_);
lean_dec_ref(v___x_3529_);
v___x_3531_ = l_Lean_mkForall(v___x_3518_, v___x_3519_, v_snd_3409_, v___x_3530_);
v___x_3532_ = l_Lean_Meta_trySynthInstance(v___x_3531_, v___x_3471_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3578_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3578_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3578_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
if (lean_obj_tag(v_a_3533_) == 1)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_del_object(v___x_3535_);
v_a_3537_ = lean_ctor_get(v_a_3533_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v_a_3533_, 1);
v___x_3538_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3539_ = l_Lean_mkConst(v___x_3538_, v___x_3487_);
v___x_3540_ = lean_unsigned_to_nat(8u);
v___x_3541_ = lean_mk_empty_array_with_capacity(v___x_3540_);
v___x_3542_ = lean_array_push(v___x_3541_, v_fst_3408_);
v___x_3543_ = lean_array_push(v___x_3542_, v_fst_3394_);
v___x_3544_ = lean_array_push(v___x_3543_, v_snd_3409_);
v___x_3545_ = lean_array_push(v___x_3544_, v_snd_3395_);
v___x_3546_ = lean_array_push(v___x_3545_, v_a_3477_);
v___x_3547_ = lean_array_push(v___x_3546_, v_a_3537_);
v___x_3548_ = lean_array_push(v___x_3547_, v_val_3510_);
v___x_3549_ = lean_array_push(v___x_3548_, v_e_3347_);
v___x_3550_ = l_Lean_mkAppN(v___x_3539_, v___x_3549_);
lean_dec_ref(v___x_3549_);
v___x_3551_ = l_Lean_Meta_expandCoe(v___x_3550_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v_fst_3553_; lean_object* v___x_3554_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v_fst_3553_ = lean_ctor_get(v_a_3552_, 0);
lean_inc_n(v_fst_3553_, 2);
lean_dec(v_a_3552_);
lean_inc(v_a_3352_);
lean_inc_ref(v_a_3351_);
lean_inc(v_a_3350_);
lean_inc_ref(v_a_3349_);
v___x_3554_ = lean_infer_type(v_fst_3553_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3556_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3554_, 1);
v___x_3556_ = l_Lean_Meta_isExprDefEq(v_a_3374_, v_a_3555_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3571_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3571_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3571_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
uint8_t v___x_3561_; 
v___x_3561_ = lean_unbox(v_a_3557_);
lean_dec(v_a_3557_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3563_; 
lean_dec(v_fst_3553_);
lean_del_object(v___x_3512_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3471_);
v___x_3563_ = v___x_3559_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3471_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
else
{
lean_object* v___x_3566_; 
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v_fst_3553_);
v___x_3566_ = v___x_3512_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_fst_3553_);
v___x_3566_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3568_; 
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3566_);
v___x_3568_ = v___x_3559_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
else
{
lean_object* v_a_3572_; 
lean_dec(v_fst_3553_);
lean_del_object(v___x_3512_);
v_a_3572_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3572_);
lean_dec_ref_known(v___x_3556_, 1);
v_a_3355_ = v_a_3572_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3573_; 
lean_dec(v_fst_3553_);
lean_del_object(v___x_3512_);
lean_dec(v_a_3374_);
v_a_3573_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v___x_3554_, 1);
v_a_3355_ = v_a_3573_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3574_; 
lean_del_object(v___x_3512_);
lean_dec(v_a_3374_);
v_a_3574_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v___x_3551_, 1);
v_a_3355_ = v_a_3574_;
goto v___jp_3354_;
}
}
else
{
lean_object* v___x_3576_; 
lean_dec(v_a_3533_);
lean_del_object(v___x_3512_);
lean_dec(v_val_3510_);
lean_dec_ref_known(v___x_3487_, 2);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3471_);
v___x_3576_ = v___x_3535_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3471_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
else
{
lean_object* v_a_3579_; 
lean_del_object(v___x_3512_);
lean_dec(v_val_3510_);
lean_dec_ref_known(v___x_3487_, 2);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3579_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3579_);
lean_dec_ref_known(v___x_3532_, 1);
v_a_3355_ = v_a_3579_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3580_; 
lean_dec(v_a_3515_);
lean_del_object(v___x_3512_);
lean_dec(v_val_3510_);
lean_dec_ref_known(v___x_3487_, 2);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3580_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3516_, 1);
v_a_3355_ = v_a_3580_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3581_; 
lean_del_object(v___x_3512_);
lean_dec(v_val_3510_);
lean_dec_ref_known(v___x_3487_, 2);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3581_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3514_, 1);
v_a_3355_ = v_a_3581_;
goto v___jp_3354_;
}
}
}
else
{
lean_object* v___x_3584_; 
lean_dec(v_a_3506_);
lean_dec_ref_known(v___x_3487_, 2);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3471_);
v___x_3584_ = v___x_3508_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3471_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
lean_object* v_a_3587_; 
lean_dec_ref_known(v___x_3487_, 2);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3587_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3587_);
lean_dec_ref_known(v___x_3505_, 1);
v_a_3355_ = v_a_3587_;
goto v___jp_3354_;
}
}
else
{
lean_object* v___x_3589_; 
lean_dec_ref_known(v___x_3487_, 2);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3496_);
v___x_3589_ = v___x_3406_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3496_);
v___x_3589_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3591_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3589_);
v___x_3591_ = v___x_3502_;
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
lean_dec_ref(v___x_3496_);
lean_dec_ref_known(v___x_3487_, 2);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3595_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3499_, 1);
v_a_3355_ = v_a_3595_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3596_; 
lean_dec_ref(v___x_3496_);
lean_dec_ref_known(v___x_3487_, 2);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3596_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3596_);
lean_dec_ref_known(v___x_3497_, 1);
v_a_3355_ = v_a_3596_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3597_; 
lean_dec(v_a_3481_);
lean_dec(v_a_3479_);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3597_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3482_, 1);
v_a_3355_ = v_a_3597_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3598_; 
lean_dec(v_a_3479_);
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3598_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3480_, 1);
v_a_3355_ = v_a_3598_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3599_; 
lean_dec(v_a_3477_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3599_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3478_, 1);
v_a_3355_ = v_a_3599_;
goto v___jp_3354_;
}
}
else
{
lean_object* v___x_3601_; 
lean_dec(v_a_3473_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3471_);
v___x_3601_ = v___x_3475_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3471_);
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
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3604_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3472_, 1);
v_a_3355_ = v_a_3604_;
goto v___jp_3354_;
}
}
}
}
else
{
lean_object* v_a_3607_; 
lean_dec(v_a_3455_);
lean_dec(v_a_3445_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3607_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3456_, 1);
v_a_3355_ = v_a_3607_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3608_; 
lean_dec(v_a_3445_);
lean_dec(v_u_3443_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3608_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3454_, 1);
v_a_3355_ = v_a_3608_;
goto v___jp_3354_;
}
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3611_; 
lean_dec(v_a_3445_);
lean_dec(v_u_3443_);
lean_dec(v_u_3435_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v___x_3609_ = lean_box(0);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3609_);
v___x_3611_ = v___x_3451_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_object* v_a_3614_; 
lean_dec(v_a_3445_);
lean_dec(v_u_3443_);
lean_dec(v_u_3435_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3614_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3448_, 1);
v_a_3355_ = v_a_3614_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3615_; 
lean_dec(v_a_3445_);
lean_dec(v_u_3443_);
lean_dec(v_u_3435_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3615_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3446_, 1);
v_a_3355_ = v_a_3615_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3616_; 
lean_dec(v_u_3443_);
lean_dec(v_u_3442_);
lean_dec(v_u_3435_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3616_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3444_, 1);
v_a_3355_ = v_a_3616_;
goto v___jp_3354_;
}
}
else
{
lean_object* v___x_3617_; 
lean_dec(v_u_3435_);
lean_dec(v_u_3434_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v___x_3617_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3439_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec_ref_known(v_a_3439_, 3);
v___y_3363_ = v___x_3617_;
goto v___jp_3362_;
}
}
else
{
lean_object* v___x_3618_; 
lean_dec(v_u_3435_);
lean_dec(v_u_3434_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v___x_3618_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3439_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec_ref_known(v_a_3439_, 3);
v___y_3363_ = v___x_3618_;
goto v___jp_3362_;
}
}
else
{
lean_object* v___x_3619_; 
lean_dec(v_u_3435_);
lean_dec(v_u_3434_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v___x_3619_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3439_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec(v_a_3439_);
v___y_3363_ = v___x_3619_;
goto v___jp_3362_;
}
}
else
{
lean_object* v_a_3620_; 
lean_dec(v_u_3435_);
lean_dec(v_u_3434_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3620_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3620_);
lean_dec_ref_known(v___x_3438_, 1);
v_a_3355_ = v_a_3620_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3621_; 
lean_dec(v_u_3435_);
lean_dec(v_u_3434_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3621_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3436_, 1);
v_a_3355_ = v_a_3621_;
goto v___jp_3354_;
}
}
else
{
lean_object* v___x_3622_; 
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v___x_3622_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3431_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec_ref_known(v_a_3431_, 3);
v___y_3363_ = v___x_3622_;
goto v___jp_3362_;
}
}
else
{
lean_object* v___x_3623_; 
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v___x_3623_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3431_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec_ref_known(v_a_3431_, 3);
v___y_3363_ = v___x_3623_;
goto v___jp_3362_;
}
}
else
{
lean_object* v___x_3624_; 
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v___x_3624_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3431_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec(v_a_3431_);
v___y_3363_ = v___x_3624_;
goto v___jp_3362_;
}
}
else
{
lean_object* v_a_3625_; 
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3625_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3430_, 1);
v_a_3355_ = v_a_3625_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3626_; 
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3626_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3428_, 1);
v_a_3355_ = v_a_3626_;
goto v___jp_3354_;
}
}
}
else
{
lean_object* v___x_3627_; 
lean_del_object(v___x_3418_);
lean_del_object(v___x_3411_);
lean_del_object(v___x_3397_);
lean_dec(v_a_3381_);
lean_dec(v_a_3374_);
v___x_3627_ = l_Lean_Meta_isMonad_x3f(v_fst_3394_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3720_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3720_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3720_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
if (lean_obj_tag(v_a_3628_) == 1)
{
lean_object* v___x_3632_; lean_object* v___x_3634_; 
v___x_3632_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v_fst_3408_);
v___x_3634_ = v___x_3406_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_fst_3408_);
v___x_3634_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
lean_object* v___x_3636_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v_snd_3409_);
v___x_3636_ = v___x_3392_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_snd_3409_);
v___x_3636_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3638_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set_tag(v___x_3383_, 1);
lean_ctor_set(v___x_3383_, 0, v_snd_3395_);
v___x_3638_ = v___x_3383_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_snd_3395_);
v___x_3638_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; lean_object* v_a_3641_; lean_object* v___x_3668_; 
v___x_3639_ = lean_box(0);
if (v_isShared_3377_ == 0)
{
lean_ctor_set_tag(v___x_3376_, 1);
lean_ctor_set(v___x_3376_, 0, v_e_3347_);
v___x_3668_ = v___x_3376_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_e_3347_);
v___x_3668_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3667_;
}
v___jp_3640_:
{
uint8_t v___x_3642_; 
v___x_3642_ = l_Lean_Exception_isInterrupt(v_a_3641_);
if (v___x_3642_ == 0)
{
uint8_t v___x_3643_; 
lean_inc_ref(v_a_3641_);
v___x_3643_ = l_Lean_Exception_isRuntime(v_a_3641_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; 
lean_dec_ref(v_a_3641_);
lean_del_object(v___x_3630_);
v___x_3644_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3414_, v_a_3350_, v_a_3352_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3651_ == 0)
{
lean_object* v_unused_3652_; 
v_unused_3652_ = lean_ctor_get(v___x_3644_, 0);
lean_dec(v_unused_3652_);
v___x_3646_ = v___x_3644_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_dec(v___x_3644_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3639_);
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3639_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
v_a_3653_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3644_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3644_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
else
{
lean_object* v___x_3662_; 
lean_dec(v_a_3414_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 0, v_a_3641_);
v___x_3662_ = v___x_3630_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3641_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
else
{
lean_object* v___x_3665_; 
lean_dec(v_a_3414_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 0, v_a_3641_);
v___x_3665_ = v___x_3630_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3641_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3669_ = lean_unsigned_to_nat(6u);
v___x_3670_ = lean_mk_empty_array_with_capacity(v___x_3669_);
v___x_3671_ = lean_array_push(v___x_3670_, v___x_3634_);
v___x_3672_ = lean_array_push(v___x_3671_, v___x_3636_);
v___x_3673_ = lean_array_push(v___x_3672_, v___x_3638_);
v___x_3674_ = lean_array_push(v___x_3673_, v___x_3639_);
v___x_3675_ = lean_array_push(v___x_3674_, v_a_3628_);
v___x_3676_ = lean_array_push(v___x_3675_, v___x_3668_);
v___x_3677_ = l_Lean_Meta_mkAppOptM(v___x_3632_, v___x_3676_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3696_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3680_ = v___x_3677_;
v_isShared_3681_ = v_isSharedCheck_3696_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3696_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Meta_expandCoe(v_a_3678_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3694_; 
lean_del_object(v___x_3630_);
lean_dec(v_a_3414_);
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3694_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3694_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v_fst_3687_; lean_object* v___x_3689_; 
v_fst_3687_ = lean_ctor_get(v_a_3683_, 0);
lean_inc(v_fst_3687_);
lean_dec(v_a_3683_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 1);
lean_ctor_set(v___x_3680_, 0, v_fst_3687_);
v___x_3689_ = v___x_3680_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_fst_3687_);
v___x_3689_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3691_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v___x_3689_);
v___x_3691_ = v___x_3685_;
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
lean_object* v_a_3695_; 
lean_del_object(v___x_3680_);
v_a_3695_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3682_, 1);
v_a_3641_ = v_a_3695_;
goto v___jp_3640_;
}
}
}
else
{
lean_object* v_a_3697_; 
v_a_3697_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___x_3677_, 1);
v_a_3641_ = v_a_3697_;
goto v___jp_3640_;
}
}
}
}
}
}
else
{
lean_object* v___x_3702_; 
lean_del_object(v___x_3630_);
lean_dec(v_a_3628_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3395_);
lean_del_object(v___x_3392_);
lean_del_object(v___x_3383_);
lean_del_object(v___x_3376_);
lean_dec_ref(v_e_3347_);
v___x_3702_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3414_, v_a_3350_, v_a_3352_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3710_; 
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; 
v_unused_3711_ = lean_ctor_get(v___x_3702_, 0);
lean_dec(v_unused_3711_);
v___x_3704_ = v___x_3702_;
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
else
{
lean_dec(v___x_3702_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3706_ = lean_box(0);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3706_);
v___x_3708_ = v___x_3704_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
v_a_3712_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3702_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3702_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3414_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3395_);
lean_del_object(v___x_3392_);
lean_del_object(v___x_3383_);
lean_del_object(v___x_3376_);
lean_dec_ref(v_e_3347_);
return v___x_3627_;
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec(v_a_3414_);
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_del_object(v___x_3392_);
lean_del_object(v___x_3383_);
lean_dec(v_a_3381_);
lean_del_object(v___x_3376_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3722_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3415_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3415_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_del_object(v___x_3411_);
lean_dec(v_snd_3409_);
lean_dec(v_fst_3408_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_del_object(v___x_3392_);
lean_del_object(v___x_3383_);
lean_dec(v_a_3381_);
lean_del_object(v___x_3376_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3730_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3413_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3413_);
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
else
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
lean_dec(v_a_3400_);
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_del_object(v___x_3392_);
lean_del_object(v___x_3383_);
lean_dec(v_a_3381_);
lean_del_object(v___x_3376_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v___x_3740_ = lean_box(0);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 0, v___x_3740_);
v___x_3742_ = v___x_3402_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
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
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_del_object(v___x_3397_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_del_object(v___x_3392_);
lean_del_object(v___x_3383_);
lean_dec(v_a_3381_);
lean_del_object(v___x_3376_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3745_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3399_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3399_);
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
}
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3757_; 
lean_dec(v_a_3386_);
lean_del_object(v___x_3383_);
lean_dec(v_a_3381_);
lean_del_object(v___x_3376_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v___x_3755_ = lean_box(0);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3755_);
v___x_3757_ = v___x_3388_;
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
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_del_object(v___x_3383_);
lean_dec(v_a_3381_);
lean_del_object(v___x_3376_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3760_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3385_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3385_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
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
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_del_object(v___x_3376_);
lean_dec(v_a_3374_);
lean_dec_ref(v_e_3347_);
v_a_3769_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3378_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3378_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3778_, lean_object* v_expectedType_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3778_, v_expectedType_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
lean_dec(v_a_3783_);
lean_dec_ref(v_a_3782_);
lean_dec(v_a_3781_);
lean_dec_ref(v_a_3780_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3786_, lean_object* v_expectedType_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v___x_3793_; 
lean_inc_ref(v_expectedType_3787_);
lean_inc_ref(v_expr_3786_);
v___x_3793_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3786_, v_expectedType_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3873_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3796_ = v___x_3793_;
v_isShared_3797_ = v_isSharedCheck_3873_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3873_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
if (lean_obj_tag(v_a_3794_) == 1)
{
lean_object* v_val_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3810_; 
lean_dec_ref(v_expectedType_3787_);
lean_dec_ref(v_expr_3786_);
v_val_3798_ = lean_ctor_get(v_a_3794_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_a_3794_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3800_ = v_a_3794_;
v_isShared_3801_ = v_isSharedCheck_3810_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_val_3798_);
lean_dec(v_a_3794_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3810_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3802_ = lean_box(0);
v___x_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3803_, 0, v_val_3798_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3803_);
v___x_3805_ = v___x_3800_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3807_; 
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3805_);
v___x_3807_ = v___x_3796_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
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
lean_object* v___x_3811_; 
lean_del_object(v___x_3796_);
lean_dec(v_a_3794_);
lean_inc_ref(v_expectedType_3787_);
v___x_3811_ = l_Lean_Meta_whnfR(v_expectedType_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; uint8_t v___x_3813_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3812_);
lean_dec_ref_known(v___x_3811_, 1);
v___x_3813_ = l_Lean_Expr_isForall(v_a_3812_);
lean_dec(v_a_3812_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3786_, v_expectedType_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
return v___x_3814_;
}
else
{
lean_object* v___x_3815_; 
lean_inc_ref(v_expr_3786_);
v___x_3815_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3786_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3815_, 1);
if (lean_obj_tag(v_a_3816_) == 1)
{
lean_object* v_val_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3855_; 
v_val_3817_ = lean_ctor_get(v_a_3816_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_a_3816_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3819_ = v_a_3816_;
v_isShared_3820_ = v_isSharedCheck_3855_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_val_3817_);
lean_dec(v_a_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3855_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; 
lean_inc(v_a_3791_);
lean_inc_ref(v_a_3790_);
lean_inc(v_a_3789_);
lean_inc_ref(v_a_3788_);
lean_inc(v_val_3817_);
v___x_3821_ = lean_infer_type(v_val_3817_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3823_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3821_, 1);
lean_inc_ref(v_expectedType_3787_);
v___x_3823_ = l_Lean_Meta_isExprDefEq(v_a_3822_, v_expectedType_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3838_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3826_ = v___x_3823_;
v_isShared_3827_ = v_isSharedCheck_3838_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3823_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3838_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
uint8_t v___x_3828_; 
v___x_3828_ = lean_unbox(v_a_3824_);
lean_dec(v_a_3824_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; 
lean_del_object(v___x_3826_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
v___x_3829_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3786_, v_expectedType_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
return v___x_3829_;
}
else
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
lean_dec_ref(v_expectedType_3787_);
lean_dec_ref(v_expr_3786_);
v___x_3830_ = lean_box(0);
v___x_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3831_, 0, v_val_3817_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3831_);
v___x_3833_ = v___x_3819_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3835_; 
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v___x_3833_);
v___x_3835_ = v___x_3826_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3833_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_expectedType_3787_);
lean_dec_ref(v_expr_3786_);
v_a_3839_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___x_3823_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3823_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
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
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_expectedType_3787_);
lean_dec_ref(v_expr_3786_);
v_a_3847_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3821_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3821_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
}
else
{
lean_object* v___x_3856_; 
lean_dec(v_a_3816_);
v___x_3856_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3786_, v_expectedType_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
return v___x_3856_;
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec_ref(v_expectedType_3787_);
lean_dec_ref(v_expr_3786_);
v_a_3857_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3815_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3815_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_dec_ref(v_expectedType_3787_);
lean_dec_ref(v_expr_3786_);
v_a_3865_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3811_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3811_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_expectedType_3787_);
lean_dec_ref(v_expr_3786_);
v_a_3874_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3793_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3793_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3882_, lean_object* v_expectedType_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3882_, v_expectedType_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
lean_dec(v_a_3887_);
lean_dec_ref(v_a_3886_);
lean_dec(v_a_3885_);
lean_dec_ref(v_a_3884_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3890_, lean_object* v_expectedType_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3890_, v_expectedType_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3922_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_3922_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3922_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
switch(lean_obj_tag(v_a_3898_))
{
case 0:
{
lean_object* v___x_3902_; lean_object* v___x_3904_; 
v___x_3902_ = lean_box(0);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3902_);
v___x_3904_ = v___x_3900_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
case 1:
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3917_; 
v_a_3906_ = lean_ctor_get(v_a_3898_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v_a_3898_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3908_ = v_a_3898_;
v_isShared_3909_ = v_isSharedCheck_3917_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v_a_3898_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3917_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v_fst_3910_; lean_object* v___x_3912_; 
v_fst_3910_ = lean_ctor_get(v_a_3906_, 0);
lean_inc(v_fst_3910_);
lean_dec(v_a_3906_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v_fst_3910_);
v___x_3912_ = v___x_3908_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_fst_3910_);
v___x_3912_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3914_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3912_);
v___x_3914_ = v___x_3900_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
default: 
{
lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3918_ = lean_box(2);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3918_);
v___x_3920_ = v___x_3900_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
v_a_3923_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3897_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3897_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3931_, lean_object* v_expectedType_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Lean_Meta_coerce_x3f(v_expr_3931_, v_expectedType_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
return v_res_3938_;
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
