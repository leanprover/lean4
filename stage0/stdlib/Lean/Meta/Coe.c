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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
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
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_187_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__0);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg(){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__1);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v___dummy_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg();
return v_res_193_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_keys_194_, lean_object* v_i_195_, lean_object* v_k_196_){
_start:
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_array_get_size(v_keys_194_);
v___x_198_ = lean_nat_dec_lt(v_i_195_, v___x_197_);
if (v___x_198_ == 0)
{
lean_dec(v_i_195_);
return v___x_198_;
}
else
{
lean_object* v_k_x27_199_; uint8_t v___x_200_; 
v_k_x27_199_ = lean_array_fget_borrowed(v_keys_194_, v_i_195_);
v___x_200_ = l_Lean_instBEqExtraModUse_beq(v_k_196_, v_k_x27_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_add(v_i_195_, v___x_201_);
lean_dec(v_i_195_);
v_i_195_ = v___x_202_;
goto _start;
}
else
{
lean_dec(v_i_195_);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_keys_204_, lean_object* v_i_205_, lean_object* v_k_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_204_, v_i_205_, v_k_206_);
lean_dec_ref(v_k_206_);
lean_dec_ref(v_keys_204_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_209_, size_t v_x_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v_es_212_; lean_object* v___x_213_; size_t v___x_214_; size_t v___x_215_; lean_object* v_j_216_; lean_object* v___x_217_; 
v_es_212_ = lean_ctor_get(v_x_209_, 0);
v___x_213_ = lean_box(2);
v___x_214_ = ((size_t)31ULL);
v___x_215_ = lean_usize_land(v_x_210_, v___x_214_);
v_j_216_ = lean_usize_to_nat(v___x_215_);
v___x_217_ = lean_array_get_borrowed(v___x_213_, v_es_212_, v_j_216_);
lean_dec(v_j_216_);
switch(lean_obj_tag(v___x_217_))
{
case 0:
{
lean_object* v_key_218_; uint8_t v___x_219_; 
v_key_218_ = lean_ctor_get(v___x_217_, 0);
v___x_219_ = l_Lean_instBEqExtraModUse_beq(v_x_211_, v_key_218_);
return v___x_219_;
}
case 1:
{
lean_object* v_node_220_; size_t v___x_221_; size_t v___x_222_; 
v_node_220_ = lean_ctor_get(v___x_217_, 0);
v___x_221_ = ((size_t)5ULL);
v___x_222_ = lean_usize_shift_right(v_x_210_, v___x_221_);
v_x_209_ = v_node_220_;
v_x_210_ = v___x_222_;
goto _start;
}
default: 
{
uint8_t v___x_224_; 
v___x_224_ = 0;
return v___x_224_;
}
}
}
else
{
lean_object* v_ks_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_ks_225_ = lean_ctor_get(v_x_209_, 0);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_225_, v___x_226_, v_x_211_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
size_t v_x_36393__boxed_231_; uint8_t v_res_232_; lean_object* v_r_233_; 
v_x_36393__boxed_231_ = lean_unbox_usize(v_x_229_);
lean_dec(v_x_229_);
v_res_232_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_228_, v_x_36393__boxed_231_, v_x_230_);
lean_dec_ref(v_x_230_);
lean_dec_ref(v_x_228_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
uint64_t v___x_236_; size_t v___x_237_; uint8_t v___x_238_; 
v___x_236_ = l_Lean_instHashableExtraModUse_hash(v_x_235_);
v___x_237_ = lean_uint64_to_usize(v___x_236_);
v___x_238_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_234_, v___x_237_, v_x_235_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_239_, v_x_240_);
lean_dec_ref(v_x_240_);
lean_dec_ref(v_x_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__7(lean_object* v_msgData_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; lean_object* v_env_250_; uint8_t v___x_251_; lean_object* v_env_252_; lean_object* v___x_253_; lean_object* v_toCold_254_; lean_object* v_mctx_255_; lean_object* v_lctx_256_; lean_object* v_options_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_249_ = lean_st_ref_get(v___y_247_);
v_env_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_env_250_);
lean_dec(v___x_249_);
v___x_251_ = 0;
v_env_252_ = l_Lean_Environment_setRecordingDeps(v_env_250_, v___x_251_);
v___x_253_ = lean_st_ref_get(v___y_245_);
v_toCold_254_ = lean_ctor_get(v___y_246_, 0);
v_mctx_255_ = lean_ctor_get(v___x_253_, 0);
lean_inc_ref(v_mctx_255_);
lean_dec(v___x_253_);
v_lctx_256_ = lean_ctor_get(v___y_244_, 2);
v_options_257_ = lean_ctor_get(v_toCold_254_, 2);
lean_inc_ref(v_options_257_);
lean_inc_ref(v_lctx_256_);
v___x_258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_258_, 0, v_env_252_);
lean_ctor_set(v___x_258_, 1, v_mctx_255_);
lean_ctor_set(v___x_258_, 2, v_lctx_256_);
lean_ctor_set(v___x_258_, 3, v_options_257_);
v___x_259_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_msgData_243_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_msgData_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__7(v_msgData_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_267_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_268_; double v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_float_of_nat(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3(lean_object* v_cls_273_, lean_object* v_msg_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_ref_281_; lean_object* v___x_282_; lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_329_; 
v_ref_281_ = lean_ctor_get(v___y_278_, 2);
v___x_282_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__7(v_msg_274_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_329_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_329_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_329_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v_traceState_288_; lean_object* v_env_289_; lean_object* v_nextMacroScope_290_; lean_object* v_ngen_291_; lean_object* v_auxDeclNGen_292_; lean_object* v_cache_293_; lean_object* v_recordedDeps_294_; lean_object* v_messages_295_; lean_object* v_infoState_296_; lean_object* v_snapshotTasks_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_328_; 
v___x_287_ = lean_st_ref_take(v___y_279_);
v_traceState_288_ = lean_ctor_get(v___x_287_, 4);
v_env_289_ = lean_ctor_get(v___x_287_, 0);
v_nextMacroScope_290_ = lean_ctor_get(v___x_287_, 1);
v_ngen_291_ = lean_ctor_get(v___x_287_, 2);
v_auxDeclNGen_292_ = lean_ctor_get(v___x_287_, 3);
v_cache_293_ = lean_ctor_get(v___x_287_, 5);
v_recordedDeps_294_ = lean_ctor_get(v___x_287_, 6);
v_messages_295_ = lean_ctor_get(v___x_287_, 7);
v_infoState_296_ = lean_ctor_get(v___x_287_, 8);
v_snapshotTasks_297_ = lean_ctor_get(v___x_287_, 9);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_328_ == 0)
{
v___x_299_ = v___x_287_;
v_isShared_300_ = v_isSharedCheck_328_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_snapshotTasks_297_);
lean_inc(v_infoState_296_);
lean_inc(v_messages_295_);
lean_inc(v_recordedDeps_294_);
lean_inc(v_cache_293_);
lean_inc(v_traceState_288_);
lean_inc(v_auxDeclNGen_292_);
lean_inc(v_ngen_291_);
lean_inc(v_nextMacroScope_290_);
lean_inc(v_env_289_);
lean_dec(v___x_287_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_328_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
uint64_t v_tid_301_; lean_object* v_traces_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_327_; 
v_tid_301_ = lean_ctor_get_uint64(v_traceState_288_, sizeof(void*)*1);
v_traces_302_ = lean_ctor_get(v_traceState_288_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_traceState_288_);
if (v_isSharedCheck_327_ == 0)
{
v___x_304_ = v_traceState_288_;
v_isShared_305_ = v_isSharedCheck_327_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_traces_302_);
lean_dec(v_traceState_288_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_327_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; double v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_306_ = lean_box(0);
v___x_307_ = lean_box(0);
v___x_308_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0);
v___x_309_ = 0;
v___x_310_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__1));
v___x_311_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_311_, 0, v_cls_273_);
lean_ctor_set(v___x_311_, 1, v___x_307_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
lean_ctor_set_float(v___x_311_, sizeof(void*)*3, v___x_308_);
lean_ctor_set_float(v___x_311_, sizeof(void*)*3 + 8, v___x_308_);
lean_ctor_set_uint8(v___x_311_, sizeof(void*)*3 + 16, v___x_309_);
v___x_312_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__2));
v___x_313_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v_a_283_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
lean_inc(v_ref_281_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v_ref_281_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = l_Lean_PersistentArray_push___redArg(v_traces_302_, v___x_314_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_315_);
v___x_317_ = v___x_304_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_315_);
lean_ctor_set_uint64(v_reuseFailAlloc_326_, sizeof(void*)*1, v_tid_301_);
v___x_317_ = v_reuseFailAlloc_326_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 4, v___x_317_);
v___x_319_ = v___x_299_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_env_289_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_nextMacroScope_290_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_ngen_291_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v_auxDeclNGen_292_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_325_, 5, v_cache_293_);
lean_ctor_set(v_reuseFailAlloc_325_, 6, v_recordedDeps_294_);
lean_ctor_set(v_reuseFailAlloc_325_, 7, v_messages_295_);
lean_ctor_set(v_reuseFailAlloc_325_, 8, v_infoState_296_);
lean_ctor_set(v_reuseFailAlloc_325_, 9, v_snapshotTasks_297_);
v___x_319_ = v_reuseFailAlloc_325_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_320_ = lean_st_ref_put(v___y_279_, v___x_319_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_306_);
lean_ctor_set(v___x_321_, 1, v___y_275_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_321_);
v___x_323_ = v___x_285_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___boxed(lean_object* v_cls_330_, lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3(v_cls_330_, v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_338_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg___closed__0);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___redArg();
return v___x_343_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0);
v___x_345_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
v___x_346_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
lean_ctor_set(v___x_346_, 2, v___x_344_);
lean_ctor_set(v___x_346_, 3, v___x_344_);
lean_ctor_set(v___x_346_, 4, v___x_344_);
lean_ctor_set(v___x_346_, 5, v___x_344_);
lean_ctor_set(v___x_346_, 6, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_347_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9));
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__1));
v___x_358_ = l_Lean_stringToMessageData(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v_cls_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_cls_362_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6));
v___x_363_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13));
v___x_364_ = l_Lean_Name_append(v___x_363_, v_cls_362_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_375_, uint8_t v_isMeta_376_, lean_object* v_hint_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_env_420_; uint8_t v_isExporting_421_; lean_object* v_entry_422_; lean_object* v___x_423_; lean_object* v_env_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_418_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_419_ = lean_st_ref_get(v___y_382_);
v_env_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_env_420_);
lean_dec(v___x_419_);
v_isExporting_421_ = lean_ctor_get_uint8(v_env_420_, sizeof(void*)*13);
lean_dec_ref(v_env_420_);
lean_inc(v_mod_375_);
v_entry_422_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_422_, 0, v_mod_375_);
lean_ctor_set_uint8(v_entry_422_, sizeof(void*)*1, v_isExporting_421_);
lean_ctor_set_uint8(v_entry_422_, sizeof(void*)*1 + 1, v_isMeta_376_);
v___x_423_ = lean_st_ref_get(v___y_382_);
v_env_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_env_424_);
lean_dec(v___x_423_);
v___x_425_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_426_ = lean_box(1);
v___x_427_ = lean_box(0);
v___x_428_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_418_, v___x_425_, v_env_424_, v___x_426_, v___x_427_);
v___x_429_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_428_, v_entry_422_);
lean_dec(v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v_toCold_430_; lean_object* v_options_431_; lean_object* v_inheritedTraceOptions_432_; uint8_t v_hasTrace_433_; lean_object* v___f_434_; uint8_t v___x_435_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; 
v_toCold_430_ = lean_ctor_get(v___y_381_, 0);
v_options_431_ = lean_ctor_get(v_toCold_430_, 2);
v_inheritedTraceOptions_432_ = lean_ctor_get(v_toCold_430_, 11);
v_hasTrace_433_ = lean_ctor_get_uint8(v_options_431_, sizeof(void*)*1);
v___f_434_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_434_, 0, v___x_425_);
lean_closure_set(v___f_434_, 1, v_entry_422_);
v___x_435_ = 1;
if (v_hasTrace_433_ == 0)
{
lean_dec(v_hint_377_);
lean_dec(v_mod_375_);
v___y_437_ = v___y_378_;
v___y_438_ = v___y_380_;
v___y_439_ = v___y_382_;
goto v___jp_436_;
}
else
{
lean_object* v_cls_466_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_cls_466_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6));
v___x_488_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14);
v___x_489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_432_, v_options_431_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec(v_hint_377_);
lean_dec(v_mod_375_);
v___y_437_ = v___y_378_;
v___y_438_ = v___y_380_;
v___y_439_ = v___y_382_;
goto v___jp_436_;
}
else
{
lean_object* v___x_490_; lean_object* v___y_492_; 
v___x_490_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
if (v_isExporting_421_ == 0)
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_492_ = v___x_499_;
goto v___jp_491_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
v___y_492_ = v___x_500_;
goto v___jp_491_;
}
v___jp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
lean_inc_ref(v___y_492_);
v___x_493_ = l_Lean_stringToMessageData(v___y_492_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_490_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
if (v_isMeta_376_ == 0)
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___y_475_ = v___x_496_;
v___y_476_ = v___x_497_;
goto v___jp_474_;
}
else
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20));
v___y_475_ = v___x_496_;
v___y_476_ = v___x_498_;
goto v___jp_474_;
}
}
}
v___jp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___y_468_);
lean_ctor_set(v___x_470_, 1, v___y_469_);
v___x_471_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3(v_cls_466_, v___x_470_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v_snd_473_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v_snd_473_ = lean_ctor_get(v_a_472_, 1);
lean_inc(v_snd_473_);
lean_dec(v_a_472_);
v___y_437_ = v_snd_473_;
v___y_438_ = v___y_380_;
v___y_439_ = v___y_382_;
goto v___jp_436_;
}
else
{
lean_dec_ref(v___f_434_);
return v___x_471_;
}
}
v___jp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
lean_inc_ref(v___y_476_);
v___x_477_ = l_Lean_stringToMessageData(v___y_476_);
v___x_478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_478_, 0, v___y_475_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8);
v___x_480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = l_Lean_MessageData_ofName(v_mod_375_);
v___x_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = l_Lean_Name_isAnonymous(v_hint_377_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_485_ = l_Lean_MessageData_ofName(v_hint_377_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___y_468_ = v___x_482_;
v___y_469_ = v___x_486_;
goto v___jp_467_;
}
else
{
lean_object* v___x_487_; 
lean_dec(v_hint_377_);
v___x_487_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11);
v___y_468_ = v___x_482_;
v___y_469_ = v___x_487_;
goto v___jp_467_;
}
}
}
v___jp_436_:
{
lean_object* v___x_440_; lean_object* v_toEnvExtension_441_; uint8_t v_logWrites_442_; 
v___x_440_ = lean_st_ref_take(v___y_439_);
v_toEnvExtension_441_ = lean_ctor_get(v___x_425_, 0);
v_logWrites_442_ = lean_ctor_get_uint8(v_toEnvExtension_441_, sizeof(void*)*6);
if (v_logWrites_442_ == 0)
{
lean_object* v_env_443_; lean_object* v_nextMacroScope_444_; lean_object* v_ngen_445_; lean_object* v_auxDeclNGen_446_; lean_object* v_traceState_447_; lean_object* v_recordedDeps_448_; lean_object* v_messages_449_; lean_object* v_infoState_450_; lean_object* v_snapshotTasks_451_; lean_object* v_asyncMode_452_; lean_object* v___x_453_; 
v_env_443_ = lean_ctor_get(v___x_440_, 0);
lean_inc_ref(v_env_443_);
v_nextMacroScope_444_ = lean_ctor_get(v___x_440_, 1);
lean_inc(v_nextMacroScope_444_);
v_ngen_445_ = lean_ctor_get(v___x_440_, 2);
lean_inc_ref(v_ngen_445_);
v_auxDeclNGen_446_ = lean_ctor_get(v___x_440_, 3);
lean_inc_ref(v_auxDeclNGen_446_);
v_traceState_447_ = lean_ctor_get(v___x_440_, 4);
lean_inc_ref(v_traceState_447_);
v_recordedDeps_448_ = lean_ctor_get(v___x_440_, 6);
lean_inc_ref(v_recordedDeps_448_);
v_messages_449_ = lean_ctor_get(v___x_440_, 7);
lean_inc_ref(v_messages_449_);
v_infoState_450_ = lean_ctor_get(v___x_440_, 8);
lean_inc_ref(v_infoState_450_);
v_snapshotTasks_451_ = lean_ctor_get(v___x_440_, 9);
lean_inc_ref(v_snapshotTasks_451_);
lean_dec(v___x_440_);
v_asyncMode_452_ = lean_ctor_get(v_toEnvExtension_441_, 2);
lean_inc_ref(v_toEnvExtension_441_);
v___x_453_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_441_, v_env_443_, v___f_434_, v_asyncMode_452_, v___x_427_, v___x_435_);
v___y_385_ = v___y_439_;
v___y_386_ = v_recordedDeps_448_;
v___y_387_ = v_nextMacroScope_444_;
v___y_388_ = v_infoState_450_;
v___y_389_ = v_traceState_447_;
v___y_390_ = v_messages_449_;
v___y_391_ = v___y_438_;
v___y_392_ = v_snapshotTasks_451_;
v___y_393_ = v_ngen_445_;
v___y_394_ = v___y_437_;
v___y_395_ = v_auxDeclNGen_446_;
v___y_396_ = v___x_453_;
goto v___jp_384_;
}
else
{
lean_object* v_env_454_; lean_object* v_nextMacroScope_455_; lean_object* v_ngen_456_; lean_object* v_auxDeclNGen_457_; lean_object* v_traceState_458_; lean_object* v_recordedDeps_459_; lean_object* v_messages_460_; lean_object* v_infoState_461_; lean_object* v_snapshotTasks_462_; lean_object* v_asyncMode_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_env_454_ = lean_ctor_get(v___x_440_, 0);
lean_inc_ref(v_env_454_);
v_nextMacroScope_455_ = lean_ctor_get(v___x_440_, 1);
lean_inc(v_nextMacroScope_455_);
v_ngen_456_ = lean_ctor_get(v___x_440_, 2);
lean_inc_ref(v_ngen_456_);
v_auxDeclNGen_457_ = lean_ctor_get(v___x_440_, 3);
lean_inc_ref(v_auxDeclNGen_457_);
v_traceState_458_ = lean_ctor_get(v___x_440_, 4);
lean_inc_ref(v_traceState_458_);
v_recordedDeps_459_ = lean_ctor_get(v___x_440_, 6);
lean_inc_ref(v_recordedDeps_459_);
v_messages_460_ = lean_ctor_get(v___x_440_, 7);
lean_inc_ref(v_messages_460_);
v_infoState_461_ = lean_ctor_get(v___x_440_, 8);
lean_inc_ref(v_infoState_461_);
v_snapshotTasks_462_ = lean_ctor_get(v___x_440_, 9);
lean_inc_ref(v_snapshotTasks_462_);
lean_dec(v___x_440_);
v_asyncMode_463_ = lean_ctor_get(v_toEnvExtension_441_, 2);
lean_inc_ref_n(v_toEnvExtension_441_, 2);
v___x_464_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_441_, v_env_454_);
lean_dec_ref(v_env_454_);
v___x_465_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_441_, v___x_464_, v___f_434_, v_asyncMode_463_, v___x_427_, v___x_435_);
v___y_385_ = v___y_439_;
v___y_386_ = v_recordedDeps_459_;
v___y_387_ = v_nextMacroScope_455_;
v___y_388_ = v_infoState_461_;
v___y_389_ = v_traceState_458_;
v___y_390_ = v_messages_460_;
v___y_391_ = v___y_438_;
v___y_392_ = v_snapshotTasks_462_;
v___y_393_ = v_ngen_456_;
v___y_394_ = v___y_437_;
v___y_395_ = v_auxDeclNGen_457_;
v___y_396_ = v___x_465_;
goto v___jp_384_;
}
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec_ref_known(v_entry_422_, 1);
lean_dec(v_hint_377_);
lean_dec(v_mod_375_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v___y_378_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
v___jp_384_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_mctx_401_; lean_object* v_zetaDeltaFVarIds_402_; lean_object* v_postponed_403_; lean_object* v_diag_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_416_; 
v___x_397_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1);
v___x_398_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_398_, 0, v___y_396_);
lean_ctor_set(v___x_398_, 1, v___y_387_);
lean_ctor_set(v___x_398_, 2, v___y_393_);
lean_ctor_set(v___x_398_, 3, v___y_395_);
lean_ctor_set(v___x_398_, 4, v___y_389_);
lean_ctor_set(v___x_398_, 5, v___x_397_);
lean_ctor_set(v___x_398_, 6, v___y_386_);
lean_ctor_set(v___x_398_, 7, v___y_390_);
lean_ctor_set(v___x_398_, 8, v___y_388_);
lean_ctor_set(v___x_398_, 9, v___y_392_);
v___x_399_ = lean_st_ref_put(v___y_385_, v___x_398_);
v___x_400_ = lean_st_ref_take(v___y_391_);
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
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_408_ = lean_box(0);
v___x_409_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v___x_409_);
v___x_411_ = v___x_406_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_mctx_401_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_zetaDeltaFVarIds_402_);
lean_ctor_set(v_reuseFailAlloc_415_, 3, v_postponed_403_);
lean_ctor_set(v_reuseFailAlloc_415_, 4, v_diag_404_);
v___x_411_ = v_reuseFailAlloc_415_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = lean_st_ref_put(v___y_391_, v___x_411_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_408_);
lean_ctor_set(v___x_413_, 1, v___y_394_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object* v_mod_504_, lean_object* v_isMeta_505_, lean_object* v_hint_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
uint8_t v_isMeta_boxed_513_; lean_object* v_res_514_; 
v_isMeta_boxed_513_ = lean_unbox(v_isMeta_505_);
v_res_514_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_504_, v_isMeta_boxed_513_, v_hint_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v___x_517_; 
v___x_517_ = lean_box(0);
return v___x_517_;
}
else
{
lean_object* v_key_518_; lean_object* v_value_519_; lean_object* v_tail_520_; uint8_t v___x_521_; 
v_key_518_ = lean_ctor_get(v_x_516_, 0);
v_value_519_ = lean_ctor_get(v_x_516_, 1);
v_tail_520_ = lean_ctor_get(v_x_516_, 2);
v___x_521_ = lean_name_eq(v_key_518_, v_a_515_);
if (v___x_521_ == 0)
{
v_x_516_ = v_tail_520_;
goto _start;
}
else
{
lean_object* v___x_523_; 
lean_inc(v_value_519_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v_value_519_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_524_, lean_object* v_x_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(v_a_524_, v_x_525_);
lean_dec(v_x_525_);
lean_dec(v_a_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_buckets_529_; lean_object* v___x_530_; uint64_t v___y_532_; 
v_buckets_529_ = lean_ctor_get(v_m_527_, 1);
v___x_530_ = lean_array_get_size(v_buckets_529_);
if (lean_obj_tag(v_a_528_) == 0)
{
uint64_t v___x_546_; 
v___x_546_ = 1723ULL;
v___y_532_ = v___x_546_;
goto v___jp_531_;
}
else
{
uint64_t v_hash_547_; 
v_hash_547_ = lean_ctor_get_uint64(v_a_528_, sizeof(void*)*2);
v___y_532_ = v_hash_547_;
goto v___jp_531_;
}
v___jp_531_:
{
uint64_t v___x_533_; uint64_t v___x_534_; uint64_t v_fold_535_; uint64_t v___x_536_; uint64_t v___x_537_; uint64_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_533_ = 32ULL;
v___x_534_ = lean_uint64_shift_right(v___y_532_, v___x_533_);
v_fold_535_ = lean_uint64_xor(v___y_532_, v___x_534_);
v___x_536_ = 16ULL;
v___x_537_ = lean_uint64_shift_right(v_fold_535_, v___x_536_);
v___x_538_ = lean_uint64_xor(v_fold_535_, v___x_537_);
v___x_539_ = lean_uint64_to_usize(v___x_538_);
v___x_540_ = lean_usize_of_nat(v___x_530_);
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_sub(v___x_540_, v___x_541_);
v___x_543_ = lean_usize_land(v___x_539_, v___x_542_);
v___x_544_ = lean_array_uget_borrowed(v_buckets_529_, v___x_543_);
v___x_545_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(v_a_528_, v___x_544_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec_ref(v_m_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_551_, lean_object* v_declName_552_, lean_object* v_as_553_, size_t v_sz_554_, size_t v_i_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_lt(v_i_555_, v_sz_554_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v_declName_552_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_b_556_);
lean_ctor_set(v___x_564_, 1, v___y_557_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
else
{
lean_object* v___x_566_; lean_object* v_modules_567_; lean_object* v___x_568_; lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v_toImport_571_; lean_object* v_module_572_; lean_object* v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; 
v___x_566_ = l_Lean_Environment_header(v___x_551_);
v_modules_567_ = lean_ctor_get(v___x_566_, 3);
lean_inc_ref(v_modules_567_);
lean_dec_ref(v___x_566_);
v___x_568_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_569_ = lean_array_uget_borrowed(v_as_553_, v_i_555_);
v___x_570_ = lean_array_get(v___x_568_, v_modules_567_, v_a_569_);
lean_dec_ref(v_modules_567_);
v_toImport_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_toImport_571_);
lean_dec(v___x_570_);
v_module_572_ = lean_ctor_get(v_toImport_571_, 0);
lean_inc(v_module_572_);
lean_dec_ref(v_toImport_571_);
v___x_573_ = lean_box(0);
v___x_574_ = 0;
lean_inc(v_declName_552_);
v___x_575_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_572_, v___x_574_, v_declName_552_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v_snd_577_; size_t v___x_578_; size_t v___x_579_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v_snd_577_ = lean_ctor_get(v_a_576_, 1);
lean_inc(v_snd_577_);
lean_dec(v_a_576_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_i_555_, v___x_578_);
v_i_555_ = v___x_579_;
v_b_556_ = v___x_573_;
v___y_557_ = v_snd_577_;
goto _start;
}
else
{
lean_dec(v_declName_552_);
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_581_, lean_object* v_declName_582_, lean_object* v_as_583_, lean_object* v_sz_584_, lean_object* v_i_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
size_t v_sz_boxed_593_; size_t v_i_boxed_594_; lean_object* v_res_595_; 
v_sz_boxed_593_ = lean_unbox_usize(v_sz_584_);
lean_dec(v_sz_584_);
v_i_boxed_594_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_res_595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_581_, v_declName_582_, v_as_583_, v_sz_boxed_593_, v_i_boxed_594_, v_b_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec_ref(v_as_583_);
lean_dec_ref(v___x_581_);
return v_res_595_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0(void){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_HashMap_instInhabited___redArg();
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_599_, uint8_t v_isMeta_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_env_613_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___x_638_; 
v___x_607_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0);
v___x_608_ = lean_st_ref_get(v___y_605_);
v_env_613_ = lean_ctor_get(v___x_608_, 0);
lean_inc_ref(v_env_613_);
lean_dec(v___x_608_);
v___x_638_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_613_, v_declName_599_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_dec_ref(v_env_613_);
lean_dec(v_declName_599_);
goto v___jp_609_;
}
else
{
lean_object* v_val_639_; lean_object* v___x_640_; lean_object* v_modules_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_val_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_val_639_);
lean_dec_ref_known(v___x_638_, 1);
v___x_640_ = l_Lean_Environment_header(v_env_613_);
v_modules_641_ = lean_ctor_get(v___x_640_, 3);
lean_inc_ref(v_modules_641_);
lean_dec_ref(v___x_640_);
v___x_642_ = lean_array_get_size(v_modules_641_);
v___x_643_ = lean_nat_dec_lt(v_val_639_, v___x_642_);
if (v___x_643_ == 0)
{
lean_dec_ref(v_modules_641_);
lean_dec(v_val_639_);
lean_dec_ref(v_env_613_);
lean_dec(v_declName_599_);
goto v___jp_609_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___y_647_; 
v___x_644_ = lean_array_fget(v_modules_641_, v_val_639_);
lean_dec(v_val_639_);
lean_dec_ref(v_modules_641_);
v___x_645_ = lean_st_ref_get(v___y_605_);
if (v_isMeta_600_ == 0)
{
lean_dec(v___x_645_);
v___y_647_ = v_isMeta_600_;
goto v___jp_646_;
}
else
{
lean_object* v_env_660_; uint8_t v___x_661_; 
v_env_660_ = lean_ctor_get(v___x_645_, 0);
lean_inc_ref(v_env_660_);
lean_dec(v___x_645_);
lean_inc(v_declName_599_);
v___x_661_ = l_Lean_isMarkedMeta(v_env_660_, v_declName_599_);
if (v___x_661_ == 0)
{
v___y_647_ = v_isMeta_600_;
goto v___jp_646_;
}
else
{
uint8_t v___x_662_; 
v___x_662_ = 0;
v___y_647_ = v___x_662_;
goto v___jp_646_;
}
}
v___jp_646_:
{
lean_object* v_toImport_648_; lean_object* v_module_649_; lean_object* v___x_650_; 
v_toImport_648_ = lean_ctor_get(v___x_644_, 0);
lean_inc_ref(v_toImport_648_);
lean_dec(v___x_644_);
v_module_649_ = lean_ctor_get(v_toImport_648_, 0);
lean_inc(v_module_649_);
lean_dec_ref(v_toImport_648_);
lean_inc(v_declName_599_);
v___x_650_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_649_, v___y_647_, v_declName_599_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v_snd_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v_snd_652_ = lean_ctor_get(v_a_651_, 1);
lean_inc(v_snd_652_);
lean_dec(v_a_651_);
v___x_653_ = l_Lean_indirectModUseExt;
v___x_654_ = lean_box(1);
v___x_655_ = lean_box(0);
lean_inc_ref(v_env_613_);
v___x_656_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_607_, v___x_653_, v_env_613_, v___x_654_, v___x_655_);
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_656_, v_declName_599_);
lean_dec(v___x_656_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v___x_658_; 
v___x_658_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___y_615_ = v_snd_652_;
v___y_616_ = v___x_658_;
goto v___jp_614_;
}
else
{
lean_object* v_val_659_; 
v_val_659_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_val_659_);
lean_dec_ref_known(v___x_657_, 1);
v___y_615_ = v_snd_652_;
v___y_616_ = v_val_659_;
goto v___jp_614_;
}
}
else
{
lean_dec_ref(v_env_613_);
lean_dec(v_declName_599_);
return v___x_650_;
}
}
}
}
v___jp_609_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_box(0);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___y_601_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
v___jp_614_:
{
lean_object* v___x_617_; size_t v_sz_618_; size_t v___x_619_; lean_object* v___x_620_; 
v___x_617_ = lean_box(0);
v_sz_618_ = lean_array_size(v___y_616_);
v___x_619_ = ((size_t)0ULL);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_613_, v_declName_599_, v___y_616_, v_sz_618_, v___x_619_, v___x_617_, v___y_615_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v_env_613_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_637_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_637_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_637_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_637_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_snd_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_635_; 
v_snd_625_ = lean_ctor_get(v_a_621_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_a_621_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_a_621_, 0);
lean_dec(v_unused_636_);
v___x_627_ = v_a_621_;
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_snd_625_);
lean_dec(v_a_621_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_617_);
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_snd_625_);
v___x_630_ = v_reuseFailAlloc_634_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_632_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_630_);
v___x_632_ = v___x_623_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
else
{
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_663_, lean_object* v_isMeta_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
uint8_t v_isMeta_boxed_671_; lean_object* v_res_672_; 
v_isMeta_boxed_671_ = lean_unbox(v_isMeta_664_);
v_res_672_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_663_, v_isMeta_boxed_671_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___y_688_; lean_object* v_f_692_; uint8_t v___x_693_; 
v_f_692_ = l_Lean_Expr_getAppFn(v_e_680_);
v___x_693_ = l_Lean_Expr_isConst(v_f_692_);
if (v___x_693_ == 0)
{
lean_dec_ref(v_f_692_);
lean_dec_ref(v_e_680_);
v___y_688_ = v___y_681_;
goto v___jp_687_;
}
else
{
lean_object* v_declName_694_; lean_object* v___x_695_; lean_object* v_env_696_; uint8_t v___x_697_; 
v_declName_694_ = l_Lean_Expr_constName_x21(v_f_692_);
lean_dec_ref(v_f_692_);
v___x_695_ = lean_st_ref_get(v___y_685_);
v_env_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_env_696_);
lean_dec(v___x_695_);
lean_inc(v_declName_694_);
v___x_697_ = l_Lean_Meta_isCoeDecl(v_env_696_, v_declName_694_);
if (v___x_697_ == 0)
{
lean_dec(v_declName_694_);
lean_dec_ref(v_e_680_);
v___y_688_ = v___y_681_;
goto v___jp_687_;
}
else
{
lean_object* v___x_698_; 
lean_inc(v_declName_694_);
lean_inc_ref(v_e_680_);
v___x_698_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_680_, v_declName_694_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; uint8_t v___x_700_; lean_object* v___x_701_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v___x_700_ = 0;
v___x_701_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_699_, v___x_700_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v_snd_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_754_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v_snd_703_ = lean_ctor_get(v_a_702_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_a_702_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v_a_702_, 0);
lean_dec(v_unused_755_);
v___x_705_ = v_a_702_;
v_isShared_706_ = v_isSharedCheck_754_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_snd_703_);
lean_dec(v_a_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_754_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; 
lean_inc_ref(v_e_680_);
v___x_707_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_680_, v___x_700_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_745_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_745_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_745_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_745_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
if (lean_obj_tag(v_a_708_) == 1)
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_744_; 
v_val_712_ = lean_ctor_get(v_a_708_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_a_708_);
if (v_isSharedCheck_744_ == 0)
{
v___x_714_ = v_a_708_;
v_isShared_715_ = v_isSharedCheck_744_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v_a_708_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_744_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___y_717_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_729_ = lean_name_eq(v_declName_694_, v___x_728_);
lean_dec(v_declName_694_);
if (v___x_729_ == 0)
{
lean_dec_ref(v_e_680_);
v___y_717_ = v_snd_703_;
goto v___jp_716_;
}
else
{
lean_object* v_dummy_730_; lean_object* v_nargs_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_dummy_730_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_731_ = l_Lean_Expr_getAppNumArgs(v_e_680_);
lean_inc(v_nargs_731_);
v___x_732_ = lean_mk_array(v_nargs_731_, v_dummy_730_);
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_nat_sub(v_nargs_731_, v___x_733_);
lean_dec(v_nargs_731_);
v___x_735_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_680_, v___x_732_, v___x_734_);
v___x_736_ = lean_unsigned_to_nat(2u);
v___x_737_ = lean_array_get_size(v___x_735_);
v___x_738_ = lean_nat_dec_lt(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_dec_ref(v___x_735_);
v___y_717_ = v_snd_703_;
goto v___jp_716_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = lean_array_fget(v___x_735_, v___x_736_);
lean_dec_ref(v___x_735_);
v___x_740_ = l_Lean_Expr_getAppFn(v___x_739_);
lean_dec(v___x_739_);
v___x_741_ = l_Lean_Expr_isConst(v___x_740_);
if (v___x_741_ == 0)
{
lean_dec_ref(v___x_740_);
v___y_717_ = v_snd_703_;
goto v___jp_716_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = l_Lean_Expr_constName_x21(v___x_740_);
lean_dec_ref(v___x_740_);
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_snd_703_);
v___y_717_ = v___x_743_;
goto v___jp_716_;
}
}
}
v___jp_716_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = l_Lean_Expr_headBeta(v_val_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_718_);
v___x_720_ = v___x_714_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_727_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v___y_717_);
lean_ctor_set(v___x_705_, 0, v___x_720_);
v___x_722_ = v___x_705_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___y_717_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_724_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_722_);
v___x_724_ = v___x_710_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_710_);
lean_dec(v_a_708_);
lean_del_object(v___x_705_);
lean_dec(v_declName_694_);
lean_dec_ref(v_e_680_);
v___y_688_ = v_snd_703_;
goto v___jp_687_;
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_del_object(v___x_705_);
lean_dec(v_snd_703_);
lean_dec(v_declName_694_);
lean_dec_ref(v_e_680_);
v_a_746_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_707_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_707_);
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
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_declName_694_);
lean_dec_ref(v_e_680_);
v_a_756_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_701_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_701_);
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
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_declName_694_);
lean_dec(v___y_681_);
lean_dec_ref(v_e_680_);
v_a_764_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_698_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_698_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
v___jp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___y_688_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Meta_expandCoe___lam__1(v_e_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0(lean_object* v_k_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; 
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
lean_inc(v___y_781_);
v___x_789_ = lean_apply_8(v_k_780_, v_b_783_, v___y_781_, v___y_782_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, lean_box(0));
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0___boxed(lean_object* v_k_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v_b_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0(v_k_790_, v___y_791_, v___y_792_, v_b_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_791_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(lean_object* v_name_800_, lean_object* v_type_801_, lean_object* v_val_802_, lean_object* v_k_803_, uint8_t v_nondep_804_, uint8_t v_kind_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___f_813_; lean_object* v___x_814_; 
lean_inc(v___y_806_);
v___f_813_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_813_, 0, v_k_803_);
lean_closure_set(v___f_813_, 1, v___y_806_);
lean_closure_set(v___f_813_, 2, v___y_807_);
v___x_814_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_800_, v_type_801_, v_val_802_, v___f_813_, v_nondep_804_, v_kind_805_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
v_a_823_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_814_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_814_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg___boxed(lean_object* v_name_831_, lean_object* v_type_832_, lean_object* v_val_833_, lean_object* v_k_834_, lean_object* v_nondep_835_, lean_object* v_kind_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
uint8_t v_nondep_boxed_844_; uint8_t v_kind_boxed_845_; lean_object* v_res_846_; 
v_nondep_boxed_844_ = lean_unbox(v_nondep_835_);
v_kind_boxed_845_ = lean_unbox(v_kind_836_);
v_res_846_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(v_name_831_, v_type_832_, v_val_833_, v_k_834_, v_nondep_boxed_844_, v_kind_boxed_845_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_837_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(lean_object* v_name_847_, uint8_t v_bi_848_, lean_object* v_type_849_, lean_object* v_k_850_, uint8_t v_kind_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___f_859_; lean_object* v___x_860_; 
lean_inc(v___y_852_);
v___f_859_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_859_, 0, v_k_850_);
lean_closure_set(v___f_859_, 1, v___y_852_);
lean_closure_set(v___f_859_, 2, v___y_853_);
v___x_860_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_847_, v_bi_848_, v_type_849_, v___f_859_, v_kind_851_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_860_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_860_);
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
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___boxed(lean_object* v_name_877_, lean_object* v_bi_878_, lean_object* v_type_879_, lean_object* v_k_880_, lean_object* v_kind_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v_bi_boxed_889_; uint8_t v_kind_boxed_890_; lean_object* v_res_891_; 
v_bi_boxed_889_ = lean_unbox(v_bi_878_);
v_kind_boxed_890_ = lean_unbox(v_kind_881_);
v_res_891_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_name_877_, v_bi_boxed_889_, v_type_879_, v_k_880_, v_kind_boxed_890_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_882_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(lean_object* v___x_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_892_);
lean_ctor_set(v___x_899_, 1, v___y_893_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed(lean_object* v___x_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(v___x_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30___redArg(lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
if (lean_obj_tag(v_x_910_) == 0)
{
return v_x_909_;
}
else
{
lean_object* v_key_911_; lean_object* v_value_912_; lean_object* v_tail_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_936_; 
v_key_911_ = lean_ctor_get(v_x_910_, 0);
v_value_912_ = lean_ctor_get(v_x_910_, 1);
v_tail_913_ = lean_ctor_get(v_x_910_, 2);
v_isSharedCheck_936_ = !lean_is_exclusive(v_x_910_);
if (v_isSharedCheck_936_ == 0)
{
v___x_915_ = v_x_910_;
v_isShared_916_ = v_isSharedCheck_936_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_tail_913_);
lean_inc(v_value_912_);
lean_inc(v_key_911_);
lean_dec(v_x_910_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_936_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; uint64_t v___x_918_; uint64_t v___x_919_; uint64_t v___x_920_; uint64_t v_fold_921_; uint64_t v___x_922_; uint64_t v___x_923_; uint64_t v___x_924_; size_t v___x_925_; size_t v___x_926_; size_t v___x_927_; size_t v___x_928_; size_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_917_ = lean_array_get_size(v_x_909_);
v___x_918_ = l_Lean_ExprStructEq_hash(v_key_911_);
v___x_919_ = 32ULL;
v___x_920_ = lean_uint64_shift_right(v___x_918_, v___x_919_);
v_fold_921_ = lean_uint64_xor(v___x_918_, v___x_920_);
v___x_922_ = 16ULL;
v___x_923_ = lean_uint64_shift_right(v_fold_921_, v___x_922_);
v___x_924_ = lean_uint64_xor(v_fold_921_, v___x_923_);
v___x_925_ = lean_uint64_to_usize(v___x_924_);
v___x_926_ = lean_usize_of_nat(v___x_917_);
v___x_927_ = ((size_t)1ULL);
v___x_928_ = lean_usize_sub(v___x_926_, v___x_927_);
v___x_929_ = lean_usize_land(v___x_925_, v___x_928_);
v___x_930_ = lean_array_uget_borrowed(v_x_909_, v___x_929_);
lean_inc(v___x_930_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 2, v___x_930_);
v___x_932_ = v___x_915_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_key_911_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_value_912_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v___x_930_);
v___x_932_ = v_reuseFailAlloc_935_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; 
v___x_933_ = lean_array_uset(v_x_909_, v___x_929_, v___x_932_);
v_x_909_ = v___x_933_;
v_x_910_ = v_tail_913_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29___redArg(lean_object* v_i_937_, lean_object* v_source_938_, lean_object* v_target_939_){
_start:
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_array_get_size(v_source_938_);
v___x_941_ = lean_nat_dec_lt(v_i_937_, v___x_940_);
if (v___x_941_ == 0)
{
lean_dec_ref(v_source_938_);
lean_dec(v_i_937_);
return v_target_939_;
}
else
{
lean_object* v_es_942_; lean_object* v___x_943_; lean_object* v_source_944_; lean_object* v_target_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_es_942_ = lean_array_fget(v_source_938_, v_i_937_);
v___x_943_ = lean_box(0);
v_source_944_ = lean_array_fset(v_source_938_, v_i_937_, v___x_943_);
v_target_945_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30___redArg(v_target_939_, v_es_942_);
v___x_946_ = lean_unsigned_to_nat(1u);
v___x_947_ = lean_nat_add(v_i_937_, v___x_946_);
lean_dec(v_i_937_);
v_i_937_ = v___x_947_;
v_source_938_ = v_source_944_;
v_target_939_ = v_target_945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(lean_object* v_data_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_nbuckets_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_950_ = lean_array_get_size(v_data_949_);
v___x_951_ = lean_unsigned_to_nat(2u);
v_nbuckets_952_ = lean_nat_mul(v___x_950_, v___x_951_);
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_box(0);
v___x_955_ = lean_mk_array(v_nbuckets_952_, v___x_954_);
v___x_956_ = lean_array_propagate_mark(v_data_949_, v___x_955_);
v___x_957_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29___redArg(v___x_953_, v_data_949_, v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(lean_object* v_a_958_, lean_object* v_x_959_){
_start:
{
if (lean_obj_tag(v_x_959_) == 0)
{
uint8_t v___x_960_; 
v___x_960_ = 0;
return v___x_960_;
}
else
{
lean_object* v_key_961_; lean_object* v_tail_962_; uint8_t v___x_963_; 
v_key_961_ = lean_ctor_get(v_x_959_, 0);
v_tail_962_ = lean_ctor_get(v_x_959_, 2);
v___x_963_ = l_Lean_ExprStructEq_beq(v_key_961_, v_a_958_);
if (v___x_963_ == 0)
{
v_x_959_ = v_tail_962_;
goto _start;
}
else
{
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg___boxed(lean_object* v_a_965_, lean_object* v_x_966_){
_start:
{
uint8_t v_res_967_; lean_object* v_r_968_; 
v_res_967_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(v_a_965_, v_x_966_);
lean_dec(v_x_966_);
lean_dec_ref(v_a_965_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28___redArg(lean_object* v_a_969_, lean_object* v_b_970_, lean_object* v_x_971_){
_start:
{
if (lean_obj_tag(v_x_971_) == 0)
{
lean_dec(v_b_970_);
lean_dec_ref(v_a_969_);
return v_x_971_;
}
else
{
lean_object* v_key_972_; lean_object* v_value_973_; lean_object* v_tail_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_986_; 
v_key_972_ = lean_ctor_get(v_x_971_, 0);
v_value_973_ = lean_ctor_get(v_x_971_, 1);
v_tail_974_ = lean_ctor_get(v_x_971_, 2);
v_isSharedCheck_986_ = !lean_is_exclusive(v_x_971_);
if (v_isSharedCheck_986_ == 0)
{
v___x_976_ = v_x_971_;
v_isShared_977_ = v_isSharedCheck_986_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_tail_974_);
lean_inc(v_value_973_);
lean_inc(v_key_972_);
lean_dec(v_x_971_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_986_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_ExprStructEq_beq(v_key_972_, v_a_969_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_979_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28___redArg(v_a_969_, v_b_970_, v_tail_974_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 2, v___x_979_);
v___x_981_ = v___x_976_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_key_972_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_value_973_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v___x_979_);
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
lean_dec(v_value_973_);
lean_dec(v_key_972_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v_b_970_);
lean_ctor_set(v___x_976_, 0, v_a_969_);
v___x_984_ = v___x_976_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_969_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_b_970_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_tail_974_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(lean_object* v_m_987_, lean_object* v_a_988_, lean_object* v_b_989_){
_start:
{
lean_object* v_size_990_; lean_object* v_buckets_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1034_; 
v_size_990_ = lean_ctor_get(v_m_987_, 0);
v_buckets_991_ = lean_ctor_get(v_m_987_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_m_987_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_993_ = v_m_987_;
v_isShared_994_ = v_isSharedCheck_1034_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_buckets_991_);
lean_inc(v_size_990_);
lean_dec(v_m_987_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1034_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; uint64_t v___x_996_; uint64_t v___x_997_; uint64_t v___x_998_; uint64_t v_fold_999_; uint64_t v___x_1000_; uint64_t v___x_1001_; uint64_t v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; size_t v___x_1006_; size_t v___x_1007_; lean_object* v_bkt_1008_; uint8_t v___x_1009_; 
v___x_995_ = lean_array_get_size(v_buckets_991_);
v___x_996_ = l_Lean_ExprStructEq_hash(v_a_988_);
v___x_997_ = 32ULL;
v___x_998_ = lean_uint64_shift_right(v___x_996_, v___x_997_);
v_fold_999_ = lean_uint64_xor(v___x_996_, v___x_998_);
v___x_1000_ = 16ULL;
v___x_1001_ = lean_uint64_shift_right(v_fold_999_, v___x_1000_);
v___x_1002_ = lean_uint64_xor(v_fold_999_, v___x_1001_);
v___x_1003_ = lean_uint64_to_usize(v___x_1002_);
v___x_1004_ = lean_usize_of_nat(v___x_995_);
v___x_1005_ = ((size_t)1ULL);
v___x_1006_ = lean_usize_sub(v___x_1004_, v___x_1005_);
v___x_1007_ = lean_usize_land(v___x_1003_, v___x_1006_);
v_bkt_1008_ = lean_array_uget_borrowed(v_buckets_991_, v___x_1007_);
v___x_1009_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(v_a_988_, v_bkt_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v_size_x27_1011_; lean_object* v___x_1012_; lean_object* v_buckets_x27_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1010_ = lean_unsigned_to_nat(1u);
v_size_x27_1011_ = lean_nat_add(v_size_990_, v___x_1010_);
lean_dec(v_size_990_);
lean_inc(v_bkt_1008_);
v___x_1012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1012_, 0, v_a_988_);
lean_ctor_set(v___x_1012_, 1, v_b_989_);
lean_ctor_set(v___x_1012_, 2, v_bkt_1008_);
v_buckets_x27_1013_ = lean_array_uset(v_buckets_991_, v___x_1007_, v___x_1012_);
v___x_1014_ = lean_unsigned_to_nat(4u);
v___x_1015_ = lean_nat_mul(v_size_x27_1011_, v___x_1014_);
v___x_1016_ = lean_unsigned_to_nat(3u);
v___x_1017_ = lean_nat_div(v___x_1015_, v___x_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_array_get_size(v_buckets_x27_1013_);
v___x_1019_ = lean_nat_dec_le(v___x_1017_, v___x_1018_);
lean_dec(v___x_1017_);
if (v___x_1019_ == 0)
{
lean_object* v_val_1020_; lean_object* v___x_1022_; 
v_val_1020_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_buckets_x27_1013_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v_val_1020_);
lean_ctor_set(v___x_993_, 0, v_size_x27_1011_);
v___x_1022_ = v___x_993_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_size_x27_1011_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_val_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
else
{
lean_object* v___x_1025_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v_buckets_x27_1013_);
lean_ctor_set(v___x_993_, 0, v_size_x27_1011_);
v___x_1025_ = v___x_993_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_size_x27_1011_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_buckets_x27_1013_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
else
{
lean_object* v___x_1027_; lean_object* v_buckets_x27_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_inc(v_bkt_1008_);
v___x_1027_ = lean_box(0);
v_buckets_x27_1028_ = lean_array_uset(v_buckets_991_, v___x_1007_, v___x_1027_);
v___x_1029_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28___redArg(v_a_988_, v_b_989_, v_bkt_1008_);
v___x_1030_ = lean_array_uset(v_buckets_x27_1028_, v___x_1007_, v___x_1029_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___x_1030_);
v___x_1032_ = v___x_993_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_size_990_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_1035_, lean_object* v_e_1036_, lean_object* v_fst_1037_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1039_ = lean_st_ref_take(v_a_1035_);
v___x_1040_ = lean_box(0);
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v___x_1039_, v_e_1036_, v_fst_1037_);
v___x_1042_ = lean_st_ref_put(v_a_1035_, v___x_1041_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_1043_, lean_object* v_e_1044_, lean_object* v_fst_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1043_, v_e_1044_, v_fst_1045_);
lean_dec(v_a_1043_);
return v_res_1047_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__3(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = l_Lean_maxRecDepthErrorMessage;
v___x_1054_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__4(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__3);
v___x_1056_ = l_Lean_MessageData_ofFormat(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__5(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__4);
v___x_1058_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__2));
v___x_1059_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object* v_ref_1060_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__5);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v_ref_1060_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object* v_ref_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_ref_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_x_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___y_1077_; lean_object* v_toCold_1094_; lean_object* v_currRecDepth_1095_; lean_object* v_ref_1096_; uint16_t v_optionFlags_1097_; uint8_t v_suppressElabErrors_1098_; uint8_t v_checkDeprecated_1099_; uint8_t v_isRecordingDeps_1100_; lean_object* v_maxRecDepth_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_toCold_1094_ = lean_ctor_get(v___y_1073_, 0);
v_currRecDepth_1095_ = lean_ctor_get(v___y_1073_, 1);
v_ref_1096_ = lean_ctor_get(v___y_1073_, 2);
v_optionFlags_1097_ = lean_ctor_get_uint16(v___y_1073_, sizeof(void*)*3);
v_suppressElabErrors_1098_ = lean_ctor_get_uint8(v___y_1073_, sizeof(void*)*3 + 2);
v_checkDeprecated_1099_ = lean_ctor_get_uint8(v___y_1073_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1100_ = lean_ctor_get_uint8(v___y_1073_, sizeof(void*)*3 + 4);
v_maxRecDepth_1106_ = lean_ctor_get(v_toCold_1094_, 3);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_nat_dec_eq(v_maxRecDepth_1106_, v___x_1107_);
if (v___x_1108_ == 0)
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_nat_dec_eq(v_currRecDepth_1095_, v_maxRecDepth_1106_);
if (v___x_1109_ == 0)
{
goto v___jp_1101_;
}
else
{
lean_object* v___x_1110_; 
lean_dec(v___y_1070_);
lean_dec_ref(v_x_1068_);
lean_inc(v_ref_1096_);
v___x_1110_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_ref_1096_);
v___y_1077_ = v___x_1110_;
goto v___jp_1076_;
}
}
else
{
goto v___jp_1101_;
}
v___jp_1076_:
{
if (lean_obj_tag(v___y_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___y_1077_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___y_1077_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___y_1077_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___y_1077_);
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
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v___y_1077_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___y_1077_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___y_1077_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___y_1077_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
v___jp_1101_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1102_ = lean_unsigned_to_nat(1u);
v___x_1103_ = lean_nat_add(v_currRecDepth_1095_, v___x_1102_);
lean_inc(v_ref_1096_);
lean_inc_ref(v_toCold_1094_);
v___x_1104_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1104_, 0, v_toCold_1094_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
lean_ctor_set(v___x_1104_, 2, v_ref_1096_);
lean_ctor_set_uint16(v___x_1104_, sizeof(void*)*3, v_optionFlags_1097_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*3 + 2, v_suppressElabErrors_1098_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*3 + 3, v_checkDeprecated_1099_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*3 + 4, v_isRecordingDeps_1100_);
lean_inc(v___y_1074_);
lean_inc(v___y_1072_);
lean_inc_ref(v___y_1071_);
lean_inc(v___y_1069_);
v___x_1105_ = lean_apply_7(v_x_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___x_1104_, v___y_1074_, lean_box(0));
v___y_1077_ = v___x_1105_;
goto v___jp_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg___boxed(lean_object* v_x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_x_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1112_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object* v_a_1120_, lean_object* v_x_1121_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object* v_a_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_a_1129_, v_x_1130_);
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
v___x_1149_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_a_1133_, v___x_1148_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1173_, lean_object* v_pre_1174_, lean_object* v_post_1175_, lean_object* v_usedLetOnly_1176_, lean_object* v_skipConstInApp_1177_, lean_object* v_skipInstances_1178_, lean_object* v_body_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
uint8_t v_usedLetOnly_boxed_1188_; uint8_t v_skipConstInApp_boxed_1189_; uint8_t v_skipInstances_boxed_1190_; lean_object* v_res_1191_; 
v_usedLetOnly_boxed_1188_ = lean_unbox(v_usedLetOnly_1176_);
v_skipConstInApp_boxed_1189_ = lean_unbox(v_skipConstInApp_1177_);
v_skipInstances_boxed_1190_ = lean_unbox(v_skipInstances_1178_);
v_res_1191_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1173_, v_pre_1174_, v_post_1175_, v_usedLetOnly_boxed_1188_, v_skipConstInApp_boxed_1189_, v_skipInstances_boxed_1190_, v_body_1179_, v_x_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1181_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1195_, lean_object* v_pre_1196_, lean_object* v_post_1197_, uint8_t v_usedLetOnly_1198_, uint8_t v_skipConstInApp_1199_, uint8_t v_skipInstances_1200_, lean_object* v_body_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_array_push(v_fvars_1195_, v_x_1202_);
v___x_1211_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1196_, v_post_1197_, v_usedLetOnly_1198_, v_skipConstInApp_1199_, v_skipInstances_1200_, v___x_1210_, v_body_1201_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1212_, lean_object* v_pre_1213_, lean_object* v_post_1214_, lean_object* v_usedLetOnly_1215_, lean_object* v_skipConstInApp_1216_, lean_object* v_skipInstances_1217_, lean_object* v_body_1218_, lean_object* v_x_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v_usedLetOnly_boxed_1227_; uint8_t v_skipConstInApp_boxed_1228_; uint8_t v_skipInstances_boxed_1229_; lean_object* v_res_1230_; 
v_usedLetOnly_boxed_1227_ = lean_unbox(v_usedLetOnly_1215_);
v_skipConstInApp_boxed_1228_ = lean_unbox(v_skipConstInApp_1216_);
v_skipInstances_boxed_1229_ = lean_unbox(v_skipInstances_1217_);
v_res_1230_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1212_, v_pre_1213_, v_post_1214_, v_usedLetOnly_boxed_1227_, v_skipConstInApp_boxed_1228_, v_skipInstances_boxed_1229_, v_body_1218_, v_x_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1220_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_pre_1231_, lean_object* v_post_1232_, uint8_t v_usedLetOnly_1233_, uint8_t v_skipConstInApp_1234_, uint8_t v_skipInstances_1235_, lean_object* v_e_1236_, lean_object* v_a_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
lean_inc_ref(v_post_1232_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc_ref(v_e_1236_);
v___x_1244_ = lean_apply_7(v_post_1232_, v_e_1236_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, lean_box(0));
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1276_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1276_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1276_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_fst_1249_; lean_object* v_snd_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1275_; 
v_fst_1249_ = lean_ctor_get(v_a_1245_, 0);
v_snd_1250_ = lean_ctor_get(v_a_1245_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_a_1245_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1252_ = v_a_1245_;
v_isShared_1253_ = v_isSharedCheck_1275_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snd_1250_);
lean_inc(v_fst_1249_);
lean_dec(v_a_1245_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1275_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___y_1255_; 
switch(lean_obj_tag(v_fst_1249_))
{
case 0:
{
lean_object* v_e_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1270_; 
lean_del_object(v___x_1252_);
lean_del_object(v___x_1247_);
lean_dec_ref(v_e_1236_);
lean_dec_ref(v_post_1232_);
lean_dec_ref(v_pre_1231_);
v_e_1262_ = lean_ctor_get(v_fst_1249_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_fst_1249_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1264_ = v_fst_1249_;
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_e_1262_);
lean_dec(v_fst_1249_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_e_1262_);
lean_ctor_set(v___x_1266_, 1, v_snd_1250_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1266_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
case 1:
{
lean_object* v_e_1271_; lean_object* v___x_1272_; 
lean_del_object(v___x_1252_);
lean_del_object(v___x_1247_);
lean_dec_ref(v_e_1236_);
v_e_1271_ = lean_ctor_get(v_fst_1249_, 0);
lean_inc_ref(v_e_1271_);
lean_dec_ref_known(v_fst_1249_, 1);
v___x_1272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1231_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v_e_1271_, v_a_1237_, v_snd_1250_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
return v___x_1272_;
}
default: 
{
lean_object* v_e_x3f_1273_; 
lean_dec_ref(v_post_1232_);
lean_dec_ref(v_pre_1231_);
v_e_x3f_1273_ = lean_ctor_get(v_fst_1249_, 0);
lean_inc(v_e_x3f_1273_);
lean_dec_ref_known(v_fst_1249_, 1);
if (lean_obj_tag(v_e_x3f_1273_) == 0)
{
v___y_1255_ = v_e_1236_;
goto v___jp_1254_;
}
else
{
lean_object* v_val_1274_; 
lean_dec_ref(v_e_1236_);
v_val_1274_ = lean_ctor_get(v_e_x3f_1273_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v_e_x3f_1273_, 1);
v___y_1255_ = v_val_1274_;
goto v___jp_1254_;
}
}
}
v___jp_1254_:
{
lean_object* v___x_1257_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___y_1255_);
v___x_1257_ = v___x_1252_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___y_1255_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_snd_1250_);
v___x_1257_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1259_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1257_);
v___x_1259_ = v___x_1247_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_e_1236_);
lean_dec_ref(v_post_1232_);
lean_dec_ref(v_pre_1231_);
v_a_1277_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1244_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1244_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1285_, lean_object* v_post_1286_, uint8_t v_usedLetOnly_1287_, uint8_t v_skipConstInApp_1288_, uint8_t v_skipInstances_1289_, lean_object* v_fvars_1290_, lean_object* v_e_1291_, lean_object* v_a_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
if (lean_obj_tag(v_e_1291_) == 6)
{
lean_object* v_binderName_1299_; lean_object* v_binderType_1300_; lean_object* v_body_1301_; uint8_t v_binderInfo_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_binderName_1299_ = lean_ctor_get(v_e_1291_, 0);
lean_inc(v_binderName_1299_);
v_binderType_1300_ = lean_ctor_get(v_e_1291_, 1);
lean_inc_ref(v_binderType_1300_);
v_body_1301_ = lean_ctor_get(v_e_1291_, 2);
lean_inc_ref(v_body_1301_);
v_binderInfo_1302_ = lean_ctor_get_uint8(v_e_1291_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1291_, 3);
v___x_1303_ = lean_box(v_usedLetOnly_1287_);
v___x_1304_ = lean_box(v_skipConstInApp_1288_);
v___x_1305_ = lean_box(v_skipInstances_1289_);
lean_inc_ref(v_post_1286_);
lean_inc_ref(v_pre_1285_);
lean_inc_ref(v_fvars_1290_);
v___f_1306_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1306_, 0, v_fvars_1290_);
lean_closure_set(v___f_1306_, 1, v_pre_1285_);
lean_closure_set(v___f_1306_, 2, v_post_1286_);
lean_closure_set(v___f_1306_, 3, v___x_1303_);
lean_closure_set(v___f_1306_, 4, v___x_1304_);
lean_closure_set(v___f_1306_, 5, v___x_1305_);
lean_closure_set(v___f_1306_, 6, v_body_1301_);
v___x_1307_ = lean_expr_instantiate_rev(v_binderType_1300_, v_fvars_1290_);
lean_dec_ref(v_fvars_1290_);
lean_dec_ref(v_binderType_1300_);
v___x_1308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1285_, v_post_1286_, v_usedLetOnly_1287_, v_skipConstInApp_1288_, v_skipInstances_1289_, v___x_1307_, v_a_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v_fst_1310_; lean_object* v_snd_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v_fst_1310_ = lean_ctor_get(v_a_1309_, 0);
lean_inc(v_fst_1310_);
v_snd_1311_ = lean_ctor_get(v_a_1309_, 1);
lean_inc(v_snd_1311_);
lean_dec(v_a_1309_);
v___x_1312_ = 0;
v___x_1313_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_binderName_1299_, v_binderInfo_1302_, v_fst_1310_, v___f_1306_, v___x_1312_, v_a_1292_, v_snd_1311_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1313_;
}
else
{
lean_dec_ref(v___f_1306_);
lean_dec(v_binderName_1299_);
return v___x_1308_;
}
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_expr_instantiate_rev(v_e_1291_, v_fvars_1290_);
lean_dec_ref(v_e_1291_);
lean_inc_ref(v_post_1286_);
lean_inc_ref(v_pre_1285_);
v___x_1315_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1285_, v_post_1286_, v_usedLetOnly_1287_, v_skipConstInApp_1288_, v_skipInstances_1289_, v___x_1314_, v_a_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v_fst_1317_; lean_object* v_snd_1318_; uint8_t v___x_1319_; uint8_t v___x_1320_; uint8_t v___x_1321_; lean_object* v___x_1322_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v_fst_1317_ = lean_ctor_get(v_a_1316_, 0);
lean_inc(v_fst_1317_);
v_snd_1318_ = lean_ctor_get(v_a_1316_, 1);
lean_inc(v_snd_1318_);
lean_dec(v_a_1316_);
v___x_1319_ = 0;
v___x_1320_ = 1;
v___x_1321_ = 1;
v___x_1322_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1290_, v_fst_1317_, v___x_1319_, v_usedLetOnly_1287_, v___x_1319_, v___x_1320_, v___x_1321_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec_ref(v_fvars_1290_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1324_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v___x_1324_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1285_, v_post_1286_, v_usedLetOnly_1287_, v_skipConstInApp_1288_, v_skipInstances_1289_, v_a_1323_, v_a_1292_, v_snd_1318_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1324_;
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_snd_1318_);
lean_dec_ref(v_post_1286_);
lean_dec_ref(v_pre_1285_);
v_a_1325_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1322_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1290_);
lean_dec_ref(v_post_1286_);
lean_dec_ref(v_pre_1285_);
return v___x_1315_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(lean_object* v_fvars_1333_, lean_object* v_pre_1334_, lean_object* v_post_1335_, uint8_t v_usedLetOnly_1336_, uint8_t v_skipConstInApp_1337_, uint8_t v_skipInstances_1338_, lean_object* v_body_1339_, lean_object* v_x_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_array_push(v_fvars_1333_, v_x_1340_);
v___x_1349_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1334_, v_post_1335_, v_usedLetOnly_1336_, v_skipConstInApp_1337_, v_skipInstances_1338_, v___x_1348_, v_body_1339_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed(lean_object* v_fvars_1350_, lean_object* v_pre_1351_, lean_object* v_post_1352_, lean_object* v_usedLetOnly_1353_, lean_object* v_skipConstInApp_1354_, lean_object* v_skipInstances_1355_, lean_object* v_body_1356_, lean_object* v_x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v_usedLetOnly_boxed_1365_; uint8_t v_skipConstInApp_boxed_1366_; uint8_t v_skipInstances_boxed_1367_; lean_object* v_res_1368_; 
v_usedLetOnly_boxed_1365_ = lean_unbox(v_usedLetOnly_1353_);
v_skipConstInApp_boxed_1366_ = lean_unbox(v_skipConstInApp_1354_);
v_skipInstances_boxed_1367_ = lean_unbox(v_skipInstances_1355_);
v_res_1368_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(v_fvars_1350_, v_pre_1351_, v_post_1352_, v_usedLetOnly_boxed_1365_, v_skipConstInApp_boxed_1366_, v_skipInstances_boxed_1367_, v_body_1356_, v_x_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1358_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(lean_object* v_pre_1369_, lean_object* v_post_1370_, uint8_t v_usedLetOnly_1371_, uint8_t v_skipConstInApp_1372_, uint8_t v_skipInstances_1373_, lean_object* v_fvars_1374_, lean_object* v_e_1375_, lean_object* v_a_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
if (lean_obj_tag(v_e_1375_) == 8)
{
lean_object* v_declName_1383_; lean_object* v_type_1384_; lean_object* v_value_1385_; lean_object* v_body_1386_; uint8_t v_nondep_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___f_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_declName_1383_ = lean_ctor_get(v_e_1375_, 0);
lean_inc(v_declName_1383_);
v_type_1384_ = lean_ctor_get(v_e_1375_, 1);
lean_inc_ref(v_type_1384_);
v_value_1385_ = lean_ctor_get(v_e_1375_, 2);
lean_inc_ref(v_value_1385_);
v_body_1386_ = lean_ctor_get(v_e_1375_, 3);
lean_inc_ref(v_body_1386_);
v_nondep_1387_ = lean_ctor_get_uint8(v_e_1375_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1375_, 4);
v___x_1388_ = lean_box(v_usedLetOnly_1371_);
v___x_1389_ = lean_box(v_skipConstInApp_1372_);
v___x_1390_ = lean_box(v_skipInstances_1373_);
lean_inc_ref_n(v_post_1370_, 2);
lean_inc_ref_n(v_pre_1369_, 2);
lean_inc_ref(v_fvars_1374_);
v___f_1391_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1391_, 0, v_fvars_1374_);
lean_closure_set(v___f_1391_, 1, v_pre_1369_);
lean_closure_set(v___f_1391_, 2, v_post_1370_);
lean_closure_set(v___f_1391_, 3, v___x_1388_);
lean_closure_set(v___f_1391_, 4, v___x_1389_);
lean_closure_set(v___f_1391_, 5, v___x_1390_);
lean_closure_set(v___f_1391_, 6, v_body_1386_);
v___x_1392_ = lean_expr_instantiate_rev(v_type_1384_, v_fvars_1374_);
lean_dec_ref(v_type_1384_);
v___x_1393_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1369_, v_post_1370_, v_usedLetOnly_1371_, v_skipConstInApp_1372_, v_skipInstances_1373_, v___x_1392_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_fst_1395_; lean_object* v_snd_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v_fst_1395_ = lean_ctor_get(v_a_1394_, 0);
lean_inc(v_fst_1395_);
v_snd_1396_ = lean_ctor_get(v_a_1394_, 1);
lean_inc(v_snd_1396_);
lean_dec(v_a_1394_);
v___x_1397_ = lean_expr_instantiate_rev(v_value_1385_, v_fvars_1374_);
lean_dec_ref(v_fvars_1374_);
lean_dec_ref(v_value_1385_);
v___x_1398_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1369_, v_post_1370_, v_usedLetOnly_1371_, v_skipConstInApp_1372_, v_skipInstances_1373_, v___x_1397_, v_a_1376_, v_snd_1396_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v_fst_1400_; lean_object* v_snd_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v_fst_1400_ = lean_ctor_get(v_a_1399_, 0);
lean_inc(v_fst_1400_);
v_snd_1401_ = lean_ctor_get(v_a_1399_, 1);
lean_inc(v_snd_1401_);
lean_dec(v_a_1399_);
v___x_1402_ = 0;
v___x_1403_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(v_declName_1383_, v_fst_1395_, v_fst_1400_, v___f_1391_, v_nondep_1387_, v___x_1402_, v_a_1376_, v_snd_1401_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
return v___x_1403_;
}
else
{
lean_dec(v_fst_1395_);
lean_dec_ref(v___f_1391_);
lean_dec(v_declName_1383_);
return v___x_1398_;
}
}
else
{
lean_dec_ref(v___f_1391_);
lean_dec_ref(v_value_1385_);
lean_dec(v_declName_1383_);
lean_dec_ref(v_fvars_1374_);
lean_dec_ref(v_post_1370_);
lean_dec_ref(v_pre_1369_);
return v___x_1393_;
}
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_expr_instantiate_rev(v_e_1375_, v_fvars_1374_);
lean_dec_ref(v_e_1375_);
lean_inc_ref(v_post_1370_);
lean_inc_ref(v_pre_1369_);
v___x_1405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1369_, v_post_1370_, v_usedLetOnly_1371_, v_skipConstInApp_1372_, v_skipInstances_1373_, v___x_1404_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_fst_1407_; lean_object* v_snd_1408_; uint8_t v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v_fst_1407_ = lean_ctor_get(v_a_1406_, 0);
lean_inc(v_fst_1407_);
v_snd_1408_ = lean_ctor_get(v_a_1406_, 1);
lean_inc(v_snd_1408_);
lean_dec(v_a_1406_);
v___x_1409_ = 0;
v___x_1410_ = 1;
v___x_1411_ = l_Lean_Meta_mkLetFVars(v_fvars_1374_, v_fst_1407_, v_usedLetOnly_1371_, v___x_1409_, v___x_1410_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec_ref(v_fvars_1374_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1369_, v_post_1370_, v_usedLetOnly_1371_, v_skipConstInApp_1372_, v_skipInstances_1373_, v_a_1412_, v_a_1376_, v_snd_1408_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
return v___x_1413_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_snd_1408_);
lean_dec_ref(v_post_1370_);
lean_dec_ref(v_pre_1369_);
v_a_1414_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1411_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1411_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1374_);
lean_dec_ref(v_post_1370_);
lean_dec_ref(v_pre_1369_);
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1422_, lean_object* v_post_1423_, uint8_t v_usedLetOnly_1424_, uint8_t v_skipConstInApp_1425_, uint8_t v_skipInstances_1426_, size_t v_sz_1427_, size_t v_i_1428_, lean_object* v_bs_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_usize_dec_lt(v_i_1428_, v_sz_1427_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref(v_post_1423_);
lean_dec_ref(v_pre_1422_);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_bs_1429_);
lean_ctor_set(v___x_1438_, 1, v___y_1431_);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
else
{
lean_object* v_v_1440_; lean_object* v___x_1441_; lean_object* v_bs_x27_1442_; lean_object* v___x_1443_; 
v_v_1440_ = lean_array_uget(v_bs_1429_, v_i_1428_);
v___x_1441_ = lean_unsigned_to_nat(0u);
v_bs_x27_1442_ = lean_array_uset(v_bs_1429_, v_i_1428_, v___x_1441_);
lean_inc_ref(v_post_1423_);
lean_inc_ref(v_pre_1422_);
v___x_1443_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1422_, v_post_1423_, v_usedLetOnly_1424_, v_skipConstInApp_1425_, v_skipInstances_1426_, v_v_1440_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v_fst_1445_; lean_object* v_snd_1446_; size_t v___x_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1443_, 1);
v_fst_1445_ = lean_ctor_get(v_a_1444_, 0);
lean_inc(v_fst_1445_);
v_snd_1446_ = lean_ctor_get(v_a_1444_, 1);
lean_inc(v_snd_1446_);
lean_dec(v_a_1444_);
v___x_1447_ = ((size_t)1ULL);
v___x_1448_ = lean_usize_add(v_i_1428_, v___x_1447_);
v___x_1449_ = lean_array_uset(v_bs_x27_1442_, v_i_1428_, v_fst_1445_);
v_i_1428_ = v___x_1448_;
v_bs_1429_ = v___x_1449_;
v___y_1431_ = v_snd_1446_;
goto _start;
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v_bs_x27_1442_);
lean_dec_ref(v_post_1423_);
lean_dec_ref(v_pre_1422_);
v_a_1451_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1443_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1443_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(lean_object* v_pre_1459_, lean_object* v_post_1460_, uint8_t v_usedLetOnly_1461_, uint8_t v_skipConstInApp_1462_, uint8_t v_skipInstances_1463_, lean_object* v___x_1464_, lean_object* v___y_1465_, lean_object* v_b_1466_, lean_object* v_a_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1459_, v_post_1460_, v_usedLetOnly_1461_, v_skipConstInApp_1462_, v_skipInstances_1463_, v___x_1464_, v___y_1465_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1493_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1493_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1493_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_fst_1479_; lean_object* v_snd_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1492_; 
v_fst_1479_ = lean_ctor_get(v_a_1475_, 0);
v_snd_1480_ = lean_ctor_get(v_a_1475_, 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_a_1475_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1482_ = v_a_1475_;
v_isShared_1483_ = v_isSharedCheck_1492_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_snd_1480_);
lean_inc(v_fst_1479_);
lean_dec(v_a_1475_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1492_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1484_ = lean_array_fset(v_b_1466_, v_a_1467_, v_fst_1479_);
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1485_);
v___x_1487_ = v___x_1482_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_snd_1480_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1487_);
v___x_1489_ = v___x_1477_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_b_1466_);
v_a_1494_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1474_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1474_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed(lean_object* v_pre_1502_, lean_object* v_post_1503_, lean_object* v_usedLetOnly_1504_, lean_object* v_skipConstInApp_1505_, lean_object* v_skipInstances_1506_, lean_object* v___x_1507_, lean_object* v___y_1508_, lean_object* v_b_1509_, lean_object* v_a_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
uint8_t v_usedLetOnly_boxed_1517_; uint8_t v_skipConstInApp_boxed_1518_; uint8_t v_skipInstances_boxed_1519_; lean_object* v_res_1520_; 
v_usedLetOnly_boxed_1517_ = lean_unbox(v_usedLetOnly_1504_);
v_skipConstInApp_boxed_1518_ = lean_unbox(v_skipConstInApp_1505_);
v_skipInstances_boxed_1519_ = lean_unbox(v_skipInstances_1506_);
v_res_1520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(v_pre_1502_, v_post_1503_, v_usedLetOnly_boxed_1517_, v_skipConstInApp_boxed_1518_, v_skipInstances_boxed_1519_, v___x_1507_, v___y_1508_, v_b_1509_, v_a_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v_a_1510_);
lean_dec(v___y_1508_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_1521_, lean_object* v___x_1522_, lean_object* v_pre_1523_, lean_object* v_post_1524_, uint8_t v_usedLetOnly_1525_, uint8_t v_skipConstInApp_1526_, uint8_t v_skipInstances_1527_, lean_object* v_a_1528_, lean_object* v_b_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___y_1538_; uint8_t v___x_1572_; 
v___x_1572_ = lean_nat_dec_lt(v_a_1528_, v_upperBound_1521_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec(v_a_1528_);
lean_dec_ref(v_post_1524_);
lean_dec_ref(v_pre_1523_);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_b_1529_);
lean_ctor_set(v___x_1573_, 1, v___y_1531_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1575_ = lean_array_fget_borrowed(v_b_1529_, v_a_1528_);
v___x_1576_ = lean_array_get_size(v___x_1522_);
v___x_1577_ = lean_nat_dec_lt(v_a_1528_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___f_1581_; 
lean_inc(v___x_1575_);
v___x_1578_ = lean_box(v_usedLetOnly_1525_);
v___x_1579_ = lean_box(v_skipConstInApp_1526_);
v___x_1580_ = lean_box(v_skipInstances_1527_);
lean_inc(v_a_1528_);
lean_inc(v___y_1530_);
lean_inc_ref(v_post_1524_);
lean_inc_ref(v_pre_1523_);
v___f_1581_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1581_, 0, v_pre_1523_);
lean_closure_set(v___f_1581_, 1, v_post_1524_);
lean_closure_set(v___f_1581_, 2, v___x_1578_);
lean_closure_set(v___f_1581_, 3, v___x_1579_);
lean_closure_set(v___f_1581_, 4, v___x_1580_);
lean_closure_set(v___f_1581_, 5, v___x_1575_);
lean_closure_set(v___f_1581_, 6, v___y_1530_);
lean_closure_set(v___f_1581_, 7, v_b_1529_);
lean_closure_set(v___f_1581_, 8, v_a_1528_);
v___y_1538_ = v___f_1581_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1582_; uint8_t v_isInstance_1583_; 
v___x_1582_ = lean_array_fget_borrowed(v___x_1522_, v_a_1528_);
v_isInstance_1583_ = lean_ctor_get_uint8(v___x_1582_, sizeof(void*)*1 + 4);
if (v_isInstance_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___f_1587_; 
lean_inc(v___x_1575_);
v___x_1584_ = lean_box(v_usedLetOnly_1525_);
v___x_1585_ = lean_box(v_skipConstInApp_1526_);
v___x_1586_ = lean_box(v_skipInstances_1527_);
lean_inc(v_a_1528_);
lean_inc(v___y_1530_);
lean_inc_ref(v_post_1524_);
lean_inc_ref(v_pre_1523_);
v___f_1587_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1587_, 0, v_pre_1523_);
lean_closure_set(v___f_1587_, 1, v_post_1524_);
lean_closure_set(v___f_1587_, 2, v___x_1584_);
lean_closure_set(v___f_1587_, 3, v___x_1585_);
lean_closure_set(v___f_1587_, 4, v___x_1586_);
lean_closure_set(v___f_1587_, 5, v___x_1575_);
lean_closure_set(v___f_1587_, 6, v___y_1530_);
lean_closure_set(v___f_1587_, 7, v_b_1529_);
lean_closure_set(v___f_1587_, 8, v_a_1528_);
v___y_1538_ = v___f_1587_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1588_; lean_object* v___f_1589_; 
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_b_1529_);
v___f_1589_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1589_, 0, v___x_1588_);
v___y_1538_ = v___f_1589_;
goto v___jp_1537_;
}
}
}
v___jp_1537_:
{
lean_object* v___x_1539_; 
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc(v___y_1533_);
lean_inc_ref(v___y_1532_);
v___x_1539_ = lean_apply_6(v___y_1538_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, lean_box(0));
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1563_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1563_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1563_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_fst_1544_; 
v_fst_1544_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_fst_1544_);
if (lean_obj_tag(v_fst_1544_) == 0)
{
lean_object* v_snd_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v_a_1528_);
lean_dec_ref(v_post_1524_);
lean_dec_ref(v_pre_1523_);
v_snd_1545_ = lean_ctor_get(v_a_1540_, 1);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_a_1540_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v_a_1540_, 0);
lean_dec(v_unused_1557_);
v___x_1547_ = v_a_1540_;
v_isShared_1548_ = v_isSharedCheck_1556_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_snd_1545_);
lean_dec(v_a_1540_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1556_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_a_1549_; lean_object* v___x_1551_; 
v_a_1549_ = lean_ctor_get(v_fst_1544_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v_fst_1544_, 1);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v_a_1549_);
v___x_1551_ = v___x_1547_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_snd_1545_);
v___x_1551_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1553_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1551_);
v___x_1553_ = v___x_1542_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v_snd_1558_; lean_object* v_a_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_del_object(v___x_1542_);
v_snd_1558_ = lean_ctor_get(v_a_1540_, 1);
lean_inc(v_snd_1558_);
lean_dec(v_a_1540_);
v_a_1559_ = lean_ctor_get(v_fst_1544_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v_fst_1544_, 1);
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_nat_add(v_a_1528_, v___x_1560_);
lean_dec(v_a_1528_);
v_a_1528_ = v___x_1561_;
v_b_1529_ = v_a_1559_;
v___y_1531_ = v_snd_1558_;
goto _start;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_a_1528_);
lean_dec_ref(v_post_1524_);
lean_dec_ref(v_pre_1523_);
v_a_1564_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1539_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1539_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(uint8_t v_skipInstances_1590_, lean_object* v_pre_1591_, lean_object* v_post_1592_, uint8_t v_usedLetOnly_1593_, uint8_t v_skipConstInApp_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_f_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; 
if (lean_obj_tag(v_x_1595_) == 5)
{
lean_object* v_fn_1661_; lean_object* v_arg_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_fn_1661_ = lean_ctor_get(v_x_1595_, 0);
lean_inc_ref(v_fn_1661_);
v_arg_1662_ = lean_ctor_get(v_x_1595_, 1);
lean_inc_ref(v_arg_1662_);
lean_dec_ref_known(v_x_1595_, 2);
v___x_1663_ = lean_array_set(v_x_1596_, v_x_1597_, v_arg_1662_);
v___x_1664_ = lean_unsigned_to_nat(1u);
v___x_1665_ = lean_nat_sub(v_x_1597_, v___x_1664_);
lean_dec(v_x_1597_);
v_x_1595_ = v_fn_1661_;
v_x_1596_ = v___x_1663_;
v_x_1597_ = v___x_1665_;
goto _start;
}
else
{
lean_dec(v_x_1597_);
if (v_skipConstInApp_1594_ == 0)
{
goto v___jp_1656_;
}
else
{
uint8_t v___x_1667_; 
v___x_1667_ = l_Lean_Expr_isConst(v_x_1595_);
if (v___x_1667_ == 0)
{
goto v___jp_1656_;
}
else
{
v_f_1606_ = v_x_1595_;
v___y_1607_ = v___y_1598_;
v___y_1608_ = v___y_1599_;
v___y_1609_ = v___y_1600_;
v___y_1610_ = v___y_1601_;
v___y_1611_ = v___y_1602_;
v___y_1612_ = v___y_1603_;
goto v___jp_1605_;
}
}
}
v___jp_1605_:
{
if (v_skipInstances_1590_ == 0)
{
size_t v_sz_1613_; size_t v___x_1614_; lean_object* v___x_1615_; 
v_sz_1613_ = lean_array_size(v_x_1596_);
v___x_1614_ = ((size_t)0ULL);
lean_inc_ref(v_post_1592_);
lean_inc_ref(v_pre_1591_);
v___x_1615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1591_, v_post_1592_, v_usedLetOnly_1593_, v_skipConstInApp_1594_, v_skipInstances_1590_, v_sz_1613_, v___x_1614_, v_x_1596_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v_fst_1617_; lean_object* v_snd_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v_fst_1617_ = lean_ctor_get(v_a_1616_, 0);
lean_inc(v_fst_1617_);
v_snd_1618_ = lean_ctor_get(v_a_1616_, 1);
lean_inc(v_snd_1618_);
lean_dec(v_a_1616_);
v___x_1619_ = l_Lean_mkAppN(v_f_1606_, v_fst_1617_);
lean_dec(v_fst_1617_);
v___x_1620_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1591_, v_post_1592_, v_usedLetOnly_1593_, v_skipConstInApp_1594_, v_skipInstances_1590_, v___x_1619_, v___y_1607_, v_snd_1618_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
return v___x_1620_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v_f_1606_);
lean_dec_ref(v_post_1592_);
lean_dec_ref(v_pre_1591_);
v_a_1621_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1615_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1615_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_array_get_size(v_x_1596_);
lean_inc_ref(v_f_1606_);
v___x_1630_ = l_Lean_Meta_getFunInfoNArgs(v_f_1606_, v___x_1629_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v_paramInfo_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v_paramInfo_1632_ = lean_ctor_get(v_a_1631_, 0);
lean_inc_ref(v_paramInfo_1632_);
lean_dec(v_a_1631_);
v___x_1633_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1592_);
lean_inc_ref(v_pre_1591_);
v___x_1634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v___x_1629_, v_paramInfo_1632_, v_pre_1591_, v_post_1592_, v_usedLetOnly_1593_, v_skipConstInApp_1594_, v_skipInstances_1590_, v___x_1633_, v_x_1596_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec_ref(v_paramInfo_1632_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v_fst_1636_; lean_object* v_snd_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v_fst_1636_ = lean_ctor_get(v_a_1635_, 0);
lean_inc(v_fst_1636_);
v_snd_1637_ = lean_ctor_get(v_a_1635_, 1);
lean_inc(v_snd_1637_);
lean_dec(v_a_1635_);
v___x_1638_ = l_Lean_mkAppN(v_f_1606_, v_fst_1636_);
lean_dec(v_fst_1636_);
v___x_1639_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1591_, v_post_1592_, v_usedLetOnly_1593_, v_skipConstInApp_1594_, v_skipInstances_1590_, v___x_1638_, v___y_1607_, v_snd_1637_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
return v___x_1639_;
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v_f_1606_);
lean_dec_ref(v_post_1592_);
lean_dec_ref(v_pre_1591_);
v_a_1640_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1634_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1634_);
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
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec(v___y_1608_);
lean_dec_ref(v_f_1606_);
lean_dec_ref(v_x_1596_);
lean_dec_ref(v_post_1592_);
lean_dec_ref(v_pre_1591_);
v_a_1648_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1630_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1630_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
v___jp_1656_:
{
lean_object* v___x_1657_; 
lean_inc_ref(v_post_1592_);
lean_inc_ref(v_pre_1591_);
v___x_1657_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1591_, v_post_1592_, v_usedLetOnly_1593_, v_skipConstInApp_1594_, v_skipInstances_1590_, v_x_1595_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v_fst_1659_; lean_object* v_snd_1660_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v_fst_1659_ = lean_ctor_get(v_a_1658_, 0);
lean_inc(v_fst_1659_);
v_snd_1660_ = lean_ctor_get(v_a_1658_, 1);
lean_inc(v_snd_1660_);
lean_dec(v_a_1658_);
v_f_1606_ = v_fst_1659_;
v___y_1607_ = v___y_1598_;
v___y_1608_ = v_snd_1660_;
v___y_1609_ = v___y_1600_;
v___y_1610_ = v___y_1601_;
v___y_1611_ = v___y_1602_;
v___y_1612_ = v___y_1603_;
goto v___jp_1605_;
}
else
{
lean_dec_ref(v_x_1596_);
lean_dec_ref(v_post_1592_);
lean_dec_ref(v_pre_1591_);
return v___x_1657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1668_, lean_object* v_pre_1669_, lean_object* v_e_1670_, lean_object* v_post_1671_, uint8_t v_usedLetOnly_1672_, uint8_t v_skipConstInApp_1673_, uint8_t v_skipInstances_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_Core_checkSystem(v___x_1668_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v___x_1683_; 
lean_dec_ref_known(v___x_1682_, 1);
lean_inc_ref(v_pre_1669_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
lean_inc_ref(v_e_1670_);
v___x_1683_ = lean_apply_7(v_pre_1669_, v_e_1670_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, lean_box(0));
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1745_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1745_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1745_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v_fst_1688_; lean_object* v_snd_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1744_; 
v_fst_1688_ = lean_ctor_get(v_a_1684_, 0);
v_snd_1689_ = lean_ctor_get(v_a_1684_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_a_1684_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1691_ = v_a_1684_;
v_isShared_1692_ = v_isSharedCheck_1744_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_snd_1689_);
lean_inc(v_fst_1688_);
lean_dec(v_a_1684_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1744_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___y_1694_; 
switch(lean_obj_tag(v_fst_1688_))
{
case 0:
{
lean_object* v_e_1733_; lean_object* v___x_1735_; 
lean_dec_ref(v_post_1671_);
lean_dec_ref(v_e_1670_);
lean_dec_ref(v_pre_1669_);
v_e_1733_ = lean_ctor_get(v_fst_1688_, 0);
lean_inc_ref(v_e_1733_);
lean_dec_ref_known(v_fst_1688_, 1);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v_e_1733_);
v___x_1735_ = v___x_1691_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_e_1733_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_snd_1689_);
v___x_1735_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1735_);
v___x_1737_ = v___x_1686_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
case 1:
{
lean_object* v_e_1740_; lean_object* v___x_1741_; 
lean_del_object(v___x_1691_);
lean_del_object(v___x_1686_);
lean_dec_ref(v_e_1670_);
v_e_1740_ = lean_ctor_get(v_fst_1688_, 0);
lean_inc_ref(v_e_1740_);
lean_dec_ref_known(v_fst_1688_, 1);
v___x_1741_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v_e_1740_, v___y_1675_, v_snd_1689_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1741_;
}
default: 
{
lean_object* v_e_x3f_1742_; 
lean_del_object(v___x_1691_);
lean_del_object(v___x_1686_);
v_e_x3f_1742_ = lean_ctor_get(v_fst_1688_, 0);
lean_inc(v_e_x3f_1742_);
lean_dec_ref_known(v_fst_1688_, 1);
if (lean_obj_tag(v_e_x3f_1742_) == 0)
{
v___y_1694_ = v_e_1670_;
goto v___jp_1693_;
}
else
{
lean_object* v_val_1743_; 
lean_dec_ref(v_e_1670_);
v_val_1743_ = lean_ctor_get(v_e_x3f_1742_, 0);
lean_inc(v_val_1743_);
lean_dec_ref_known(v_e_x3f_1742_, 1);
v___y_1694_ = v_val_1743_;
goto v___jp_1693_;
}
}
}
v___jp_1693_:
{
switch(lean_obj_tag(v___y_1694_))
{
case 7:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1696_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v___x_1695_, v___y_1694_, v___y_1675_, v_snd_1689_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1696_;
}
case 6:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1698_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v___x_1697_, v___y_1694_, v___y_1675_, v_snd_1689_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1698_;
}
case 8:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1700_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v___x_1699_, v___y_1694_, v___y_1675_, v_snd_1689_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1700_;
}
case 5:
{
lean_object* v_dummy_1701_; lean_object* v_nargs_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_dummy_1701_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1702_ = l_Lean_Expr_getAppNumArgs(v___y_1694_);
lean_inc(v_nargs_1702_);
v___x_1703_ = lean_mk_array(v_nargs_1702_, v_dummy_1701_);
v___x_1704_ = lean_unsigned_to_nat(1u);
v___x_1705_ = lean_nat_sub(v_nargs_1702_, v___x_1704_);
lean_dec(v_nargs_1702_);
v___x_1706_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_skipInstances_1674_, v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v___y_1694_, v___x_1703_, v___x_1705_, v___y_1675_, v_snd_1689_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1706_;
}
case 10:
{
lean_object* v_data_1707_; lean_object* v_expr_1708_; lean_object* v___x_1709_; 
v_data_1707_ = lean_ctor_get(v___y_1694_, 0);
v_expr_1708_ = lean_ctor_get(v___y_1694_, 1);
lean_inc_ref(v_expr_1708_);
lean_inc_ref(v_post_1671_);
lean_inc_ref(v_pre_1669_);
v___x_1709_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v_expr_1708_, v___y_1675_, v_snd_1689_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v_fst_1711_; lean_object* v_snd_1712_; size_t v___x_1713_; size_t v___x_1714_; uint8_t v___x_1715_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v_fst_1711_ = lean_ctor_get(v_a_1710_, 0);
lean_inc(v_fst_1711_);
v_snd_1712_ = lean_ctor_get(v_a_1710_, 1);
lean_inc(v_snd_1712_);
lean_dec(v_a_1710_);
v___x_1713_ = lean_ptr_addr(v_expr_1708_);
v___x_1714_ = lean_ptr_addr(v_fst_1711_);
v___x_1715_ = lean_usize_dec_eq(v___x_1713_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_inc(v_data_1707_);
lean_dec_ref_known(v___y_1694_, 2);
v___x_1716_ = l_Lean_Expr_mdata___override(v_data_1707_, v_fst_1711_);
v___x_1717_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v___x_1716_, v___y_1675_, v_snd_1712_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; 
lean_dec(v_fst_1711_);
v___x_1718_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v___y_1694_, v___y_1675_, v_snd_1712_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1718_;
}
}
else
{
lean_dec_ref_known(v___y_1694_, 2);
lean_dec_ref(v_post_1671_);
lean_dec_ref(v_pre_1669_);
return v___x_1709_;
}
}
case 11:
{
lean_object* v_typeName_1719_; lean_object* v_idx_1720_; lean_object* v_struct_1721_; lean_object* v___x_1722_; 
v_typeName_1719_ = lean_ctor_get(v___y_1694_, 0);
v_idx_1720_ = lean_ctor_get(v___y_1694_, 1);
v_struct_1721_ = lean_ctor_get(v___y_1694_, 2);
lean_inc_ref(v_struct_1721_);
lean_inc_ref(v_post_1671_);
lean_inc_ref(v_pre_1669_);
v___x_1722_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v_struct_1721_, v___y_1675_, v_snd_1689_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v_fst_1724_; lean_object* v_snd_1725_; size_t v___x_1726_; size_t v___x_1727_; uint8_t v___x_1728_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v_fst_1724_ = lean_ctor_get(v_a_1723_, 0);
lean_inc(v_fst_1724_);
v_snd_1725_ = lean_ctor_get(v_a_1723_, 1);
lean_inc(v_snd_1725_);
lean_dec(v_a_1723_);
v___x_1726_ = lean_ptr_addr(v_struct_1721_);
v___x_1727_ = lean_ptr_addr(v_fst_1724_);
v___x_1728_ = lean_usize_dec_eq(v___x_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_inc(v_idx_1720_);
lean_inc(v_typeName_1719_);
lean_dec_ref_known(v___y_1694_, 3);
v___x_1729_ = l_Lean_Expr_proj___override(v_typeName_1719_, v_idx_1720_, v_fst_1724_);
v___x_1730_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v___x_1729_, v___y_1675_, v_snd_1725_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_fst_1724_);
v___x_1731_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v___y_1694_, v___y_1675_, v_snd_1725_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1731_;
}
}
else
{
lean_dec_ref_known(v___y_1694_, 3);
lean_dec_ref(v_post_1671_);
lean_dec_ref(v_pre_1669_);
return v___x_1722_;
}
}
default: 
{
lean_object* v___x_1732_; 
v___x_1732_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1669_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v___y_1694_, v___y_1675_, v_snd_1689_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1732_;
}
}
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec_ref(v_post_1671_);
lean_dec_ref(v_e_1670_);
lean_dec_ref(v_pre_1669_);
v_a_1746_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1683_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1683_);
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
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v___y_1676_);
lean_dec_ref(v_post_1671_);
lean_dec_ref(v_e_1670_);
lean_dec_ref(v_pre_1669_);
v_a_1754_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1682_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1682_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1762_, lean_object* v_pre_1763_, lean_object* v_e_1764_, lean_object* v_post_1765_, lean_object* v_usedLetOnly_1766_, lean_object* v_skipConstInApp_1767_, lean_object* v_skipInstances_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
uint8_t v_usedLetOnly_boxed_1776_; uint8_t v_skipConstInApp_boxed_1777_; uint8_t v_skipInstances_boxed_1778_; lean_object* v_res_1779_; 
v_usedLetOnly_boxed_1776_ = lean_unbox(v_usedLetOnly_1766_);
v_skipConstInApp_boxed_1777_ = lean_unbox(v_skipConstInApp_1767_);
v_skipInstances_boxed_1778_ = lean_unbox(v_skipInstances_1768_);
v_res_1779_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1762_, v_pre_1763_, v_e_1764_, v_post_1765_, v_usedLetOnly_boxed_1776_, v_skipConstInApp_boxed_1777_, v_skipInstances_boxed_1778_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1769_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1780_, lean_object* v_post_1781_, uint8_t v_usedLetOnly_1782_, uint8_t v_skipConstInApp_1783_, uint8_t v_skipInstances_1784_, lean_object* v_e_1785_, lean_object* v_a_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_inc(v_a_1786_);
v___x_1793_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1793_, 0, lean_box(0));
lean_closure_set(v___x_1793_, 1, lean_box(0));
lean_closure_set(v___x_1793_, 2, v_a_1786_);
v___x_1794_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1793_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1849_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1849_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1849_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1848_; 
v_fst_1799_ = lean_ctor_get(v_a_1795_, 0);
v_snd_1800_ = lean_ctor_get(v_a_1795_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_a_1795_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1802_ = v_a_1795_;
v_isShared_1803_ = v_isSharedCheck_1848_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_snd_1800_);
lean_inc(v_fst_1799_);
lean_dec(v_a_1795_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1848_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_fst_1799_, v_e_1785_);
lean_dec(v_fst_1799_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___f_1809_; lean_object* v___x_1810_; 
lean_del_object(v___x_1802_);
lean_del_object(v___x_1797_);
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1806_ = lean_box(v_usedLetOnly_1782_);
v___x_1807_ = lean_box(v_skipConstInApp_1783_);
v___x_1808_ = lean_box(v_skipInstances_1784_);
lean_inc_ref(v_e_1785_);
v___f_1809_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1809_, 0, v___x_1805_);
lean_closure_set(v___f_1809_, 1, v_pre_1780_);
lean_closure_set(v___f_1809_, 2, v_e_1785_);
lean_closure_set(v___f_1809_, 3, v_post_1781_);
lean_closure_set(v___f_1809_, 4, v___x_1806_);
lean_closure_set(v___f_1809_, 5, v___x_1807_);
lean_closure_set(v___f_1809_, 6, v___x_1808_);
v___x_1810_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___f_1809_, v_a_1786_, v_snd_1800_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v_fst_1812_; lean_object* v_snd_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v_fst_1812_ = lean_ctor_get(v_a_1811_, 0);
lean_inc_n(v_fst_1812_, 2);
v_snd_1813_ = lean_ctor_get(v_a_1811_, 1);
lean_inc(v_snd_1813_);
lean_dec(v_a_1811_);
lean_inc(v_a_1786_);
v___f_1814_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1814_, 0, v_a_1786_);
lean_closure_set(v___f_1814_, 1, v_e_1785_);
lean_closure_set(v___f_1814_, 2, v_fst_1812_);
v___x_1815_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1814_, v_snd_1813_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1832_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1832_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1832_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_snd_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1830_; 
v_snd_1820_ = lean_ctor_get(v_a_1816_, 1);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_a_1816_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; 
v_unused_1831_ = lean_ctor_get(v_a_1816_, 0);
lean_dec(v_unused_1831_);
v___x_1822_ = v_a_1816_;
v_isShared_1823_ = v_isSharedCheck_1830_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_snd_1820_);
lean_dec(v_a_1816_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1830_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v_fst_1812_);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_fst_1812_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_snd_1820_);
v___x_1825_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1827_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1825_);
v___x_1827_ = v___x_1818_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec(v_fst_1812_);
v_a_1833_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1815_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1815_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_dec_ref(v_e_1785_);
return v___x_1810_;
}
}
else
{
lean_object* v_val_1841_; lean_object* v___x_1843_; 
lean_dec_ref(v_e_1785_);
lean_dec_ref(v_post_1781_);
lean_dec_ref(v_pre_1780_);
v_val_1841_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1841_);
lean_dec_ref_known(v___x_1804_, 1);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v_val_1841_);
v___x_1843_ = v___x_1802_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_val_1841_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_snd_1800_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1843_);
v___x_1845_ = v___x_1797_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v_e_1785_);
lean_dec_ref(v_post_1781_);
lean_dec_ref(v_pre_1780_);
v_a_1850_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1794_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1794_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1858_, lean_object* v_post_1859_, uint8_t v_usedLetOnly_1860_, uint8_t v_skipConstInApp_1861_, uint8_t v_skipInstances_1862_, lean_object* v_fvars_1863_, lean_object* v_e_1864_, lean_object* v_a_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
if (lean_obj_tag(v_e_1864_) == 7)
{
lean_object* v_binderName_1872_; lean_object* v_binderType_1873_; lean_object* v_body_1874_; uint8_t v_binderInfo_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___f_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_binderName_1872_ = lean_ctor_get(v_e_1864_, 0);
lean_inc(v_binderName_1872_);
v_binderType_1873_ = lean_ctor_get(v_e_1864_, 1);
lean_inc_ref(v_binderType_1873_);
v_body_1874_ = lean_ctor_get(v_e_1864_, 2);
lean_inc_ref(v_body_1874_);
v_binderInfo_1875_ = lean_ctor_get_uint8(v_e_1864_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1864_, 3);
v___x_1876_ = lean_box(v_usedLetOnly_1860_);
v___x_1877_ = lean_box(v_skipConstInApp_1861_);
v___x_1878_ = lean_box(v_skipInstances_1862_);
lean_inc_ref(v_post_1859_);
lean_inc_ref(v_pre_1858_);
lean_inc_ref(v_fvars_1863_);
v___f_1879_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1879_, 0, v_fvars_1863_);
lean_closure_set(v___f_1879_, 1, v_pre_1858_);
lean_closure_set(v___f_1879_, 2, v_post_1859_);
lean_closure_set(v___f_1879_, 3, v___x_1876_);
lean_closure_set(v___f_1879_, 4, v___x_1877_);
lean_closure_set(v___f_1879_, 5, v___x_1878_);
lean_closure_set(v___f_1879_, 6, v_body_1874_);
v___x_1880_ = lean_expr_instantiate_rev(v_binderType_1873_, v_fvars_1863_);
lean_dec_ref(v_fvars_1863_);
lean_dec_ref(v_binderType_1873_);
v___x_1881_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1858_, v_post_1859_, v_usedLetOnly_1860_, v_skipConstInApp_1861_, v_skipInstances_1862_, v___x_1880_, v_a_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v_fst_1883_; lean_object* v_snd_1884_; uint8_t v___x_1885_; lean_object* v___x_1886_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v_fst_1883_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_fst_1883_);
v_snd_1884_ = lean_ctor_get(v_a_1882_, 1);
lean_inc(v_snd_1884_);
lean_dec(v_a_1882_);
v___x_1885_ = 0;
v___x_1886_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_binderName_1872_, v_binderInfo_1875_, v_fst_1883_, v___f_1879_, v___x_1885_, v_a_1865_, v_snd_1884_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
return v___x_1886_;
}
else
{
lean_dec_ref(v___f_1879_);
lean_dec(v_binderName_1872_);
return v___x_1881_;
}
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_expr_instantiate_rev(v_e_1864_, v_fvars_1863_);
lean_dec_ref(v_e_1864_);
lean_inc_ref(v_post_1859_);
lean_inc_ref(v_pre_1858_);
v___x_1888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1858_, v_post_1859_, v_usedLetOnly_1860_, v_skipConstInApp_1861_, v_skipInstances_1862_, v___x_1887_, v_a_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v_fst_1890_; lean_object* v_snd_1891_; uint8_t v___x_1892_; uint8_t v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v_fst_1890_ = lean_ctor_get(v_a_1889_, 0);
lean_inc(v_fst_1890_);
v_snd_1891_ = lean_ctor_get(v_a_1889_, 1);
lean_inc(v_snd_1891_);
lean_dec(v_a_1889_);
v___x_1892_ = 0;
v___x_1893_ = 1;
v___x_1894_ = 1;
v___x_1895_ = l_Lean_Meta_mkForallFVars(v_fvars_1863_, v_fst_1890_, v___x_1892_, v_usedLetOnly_1860_, v___x_1893_, v___x_1894_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec_ref(v_fvars_1863_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1858_, v_post_1859_, v_usedLetOnly_1860_, v_skipConstInApp_1861_, v_skipInstances_1862_, v_a_1896_, v_a_1865_, v_snd_1891_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
return v___x_1897_;
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_snd_1891_);
lean_dec_ref(v_post_1859_);
lean_dec_ref(v_pre_1858_);
v_a_1898_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1895_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1895_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1863_);
lean_dec_ref(v_post_1859_);
lean_dec_ref(v_pre_1858_);
return v___x_1888_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1906_, lean_object* v_pre_1907_, lean_object* v_post_1908_, uint8_t v_usedLetOnly_1909_, uint8_t v_skipConstInApp_1910_, uint8_t v_skipInstances_1911_, lean_object* v_body_1912_, lean_object* v_x_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_array_push(v_fvars_1906_, v_x_1913_);
v___x_1922_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1907_, v_post_1908_, v_usedLetOnly_1909_, v_skipConstInApp_1910_, v_skipInstances_1911_, v___x_1921_, v_body_1912_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1923_, lean_object* v_post_1924_, lean_object* v_usedLetOnly_1925_, lean_object* v_skipConstInApp_1926_, lean_object* v_skipInstances_1927_, lean_object* v_sz_1928_, lean_object* v_i_1929_, lean_object* v_bs_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
uint8_t v_usedLetOnly_boxed_1938_; uint8_t v_skipConstInApp_boxed_1939_; uint8_t v_skipInstances_boxed_1940_; size_t v_sz_boxed_1941_; size_t v_i_boxed_1942_; lean_object* v_res_1943_; 
v_usedLetOnly_boxed_1938_ = lean_unbox(v_usedLetOnly_1925_);
v_skipConstInApp_boxed_1939_ = lean_unbox(v_skipConstInApp_1926_);
v_skipInstances_boxed_1940_ = lean_unbox(v_skipInstances_1927_);
v_sz_boxed_1941_ = lean_unbox_usize(v_sz_1928_);
lean_dec(v_sz_1928_);
v_i_boxed_1942_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_res_1943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1923_, v_post_1924_, v_usedLetOnly_boxed_1938_, v_skipConstInApp_boxed_1939_, v_skipInstances_boxed_1940_, v_sz_boxed_1941_, v_i_boxed_1942_, v_bs_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1931_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object* v_pre_1944_, lean_object* v_post_1945_, lean_object* v_usedLetOnly_1946_, lean_object* v_skipConstInApp_1947_, lean_object* v_skipInstances_1948_, lean_object* v_e_1949_, lean_object* v_a_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
uint8_t v_usedLetOnly_boxed_1957_; uint8_t v_skipConstInApp_boxed_1958_; uint8_t v_skipInstances_boxed_1959_; lean_object* v_res_1960_; 
v_usedLetOnly_boxed_1957_ = lean_unbox(v_usedLetOnly_1946_);
v_skipConstInApp_boxed_1958_ = lean_unbox(v_skipConstInApp_1947_);
v_skipInstances_boxed_1959_ = lean_unbox(v_skipInstances_1948_);
v_res_1960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1944_, v_post_1945_, v_usedLetOnly_boxed_1957_, v_skipConstInApp_boxed_1958_, v_skipInstances_boxed_1959_, v_e_1949_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_a_1950_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1961_, lean_object* v_post_1962_, lean_object* v_usedLetOnly_1963_, lean_object* v_skipConstInApp_1964_, lean_object* v_skipInstances_1965_, lean_object* v_fvars_1966_, lean_object* v_e_1967_, lean_object* v_a_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
uint8_t v_usedLetOnly_boxed_1975_; uint8_t v_skipConstInApp_boxed_1976_; uint8_t v_skipInstances_boxed_1977_; lean_object* v_res_1978_; 
v_usedLetOnly_boxed_1975_ = lean_unbox(v_usedLetOnly_1963_);
v_skipConstInApp_boxed_1976_ = lean_unbox(v_skipConstInApp_1964_);
v_skipInstances_boxed_1977_ = lean_unbox(v_skipInstances_1965_);
v_res_1978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1961_, v_post_1962_, v_usedLetOnly_boxed_1975_, v_skipConstInApp_boxed_1976_, v_skipInstances_boxed_1977_, v_fvars_1966_, v_e_1967_, v_a_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v_a_1968_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1979_, lean_object* v_post_1980_, lean_object* v_usedLetOnly_1981_, lean_object* v_skipConstInApp_1982_, lean_object* v_skipInstances_1983_, lean_object* v_fvars_1984_, lean_object* v_e_1985_, lean_object* v_a_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
uint8_t v_usedLetOnly_boxed_1993_; uint8_t v_skipConstInApp_boxed_1994_; uint8_t v_skipInstances_boxed_1995_; lean_object* v_res_1996_; 
v_usedLetOnly_boxed_1993_ = lean_unbox(v_usedLetOnly_1981_);
v_skipConstInApp_boxed_1994_ = lean_unbox(v_skipConstInApp_1982_);
v_skipInstances_boxed_1995_ = lean_unbox(v_skipInstances_1983_);
v_res_1996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1979_, v_post_1980_, v_usedLetOnly_boxed_1993_, v_skipConstInApp_boxed_1994_, v_skipInstances_boxed_1995_, v_fvars_1984_, v_e_1985_, v_a_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v_a_1986_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1997_, lean_object* v_post_1998_, lean_object* v_usedLetOnly_1999_, lean_object* v_skipConstInApp_2000_, lean_object* v_skipInstances_2001_, lean_object* v_e_2002_, lean_object* v_a_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
uint8_t v_usedLetOnly_boxed_2010_; uint8_t v_skipConstInApp_boxed_2011_; uint8_t v_skipInstances_boxed_2012_; lean_object* v_res_2013_; 
v_usedLetOnly_boxed_2010_ = lean_unbox(v_usedLetOnly_1999_);
v_skipConstInApp_boxed_2011_ = lean_unbox(v_skipConstInApp_2000_);
v_skipInstances_boxed_2012_ = lean_unbox(v_skipInstances_2001_);
v_res_2013_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1997_, v_post_1998_, v_usedLetOnly_boxed_2010_, v_skipConstInApp_boxed_2011_, v_skipInstances_boxed_2012_, v_e_2002_, v_a_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v_a_2003_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_pre_2014_, lean_object* v_post_2015_, lean_object* v_usedLetOnly_2016_, lean_object* v_skipConstInApp_2017_, lean_object* v_skipInstances_2018_, lean_object* v_fvars_2019_, lean_object* v_e_2020_, lean_object* v_a_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
uint8_t v_usedLetOnly_boxed_2028_; uint8_t v_skipConstInApp_boxed_2029_; uint8_t v_skipInstances_boxed_2030_; lean_object* v_res_2031_; 
v_usedLetOnly_boxed_2028_ = lean_unbox(v_usedLetOnly_2016_);
v_skipConstInApp_boxed_2029_ = lean_unbox(v_skipConstInApp_2017_);
v_skipInstances_boxed_2030_ = lean_unbox(v_skipInstances_2018_);
v_res_2031_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_2014_, v_post_2015_, v_usedLetOnly_boxed_2028_, v_skipConstInApp_boxed_2029_, v_skipInstances_boxed_2030_, v_fvars_2019_, v_e_2020_, v_a_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v_a_2021_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_upperBound_2032_, lean_object* v___x_2033_, lean_object* v_pre_2034_, lean_object* v_post_2035_, lean_object* v_usedLetOnly_2036_, lean_object* v_skipConstInApp_2037_, lean_object* v_skipInstances_2038_, lean_object* v_a_2039_, lean_object* v_b_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v_usedLetOnly_boxed_2048_; uint8_t v_skipConstInApp_boxed_2049_; uint8_t v_skipInstances_boxed_2050_; lean_object* v_res_2051_; 
v_usedLetOnly_boxed_2048_ = lean_unbox(v_usedLetOnly_2036_);
v_skipConstInApp_boxed_2049_ = lean_unbox(v_skipConstInApp_2037_);
v_skipInstances_boxed_2050_ = lean_unbox(v_skipInstances_2038_);
v_res_2051_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_upperBound_2032_, v___x_2033_, v_pre_2034_, v_post_2035_, v_usedLetOnly_boxed_2048_, v_skipConstInApp_boxed_2049_, v_skipInstances_boxed_2050_, v_a_2039_, v_b_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2041_);
lean_dec_ref(v___x_2033_);
lean_dec(v_upperBound_2032_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_skipInstances_2052_, lean_object* v_pre_2053_, lean_object* v_post_2054_, lean_object* v_usedLetOnly_2055_, lean_object* v_skipConstInApp_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_, lean_object* v_x_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
uint8_t v_skipInstances_boxed_2067_; uint8_t v_usedLetOnly_boxed_2068_; uint8_t v_skipConstInApp_boxed_2069_; lean_object* v_res_2070_; 
v_skipInstances_boxed_2067_ = lean_unbox(v_skipInstances_2052_);
v_usedLetOnly_boxed_2068_ = lean_unbox(v_usedLetOnly_2055_);
v_skipConstInApp_boxed_2069_ = lean_unbox(v_skipConstInApp_2056_);
v_res_2070_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_skipInstances_boxed_2067_, v_pre_2053_, v_post_2054_, v_usedLetOnly_boxed_2068_, v_skipConstInApp_boxed_2069_, v_x_2057_, v_x_2058_, v_x_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2060_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2071_, lean_object* v_x_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_apply_1(v_x_2072_, lean_box(0));
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___y_2073_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2082_, lean_object* v_x_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2082_, v_x_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2090_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = lean_unsigned_to_nat(16u);
v___x_2093_ = lean_mk_array(v___x_2092_, v___x_2091_);
return v___x_2093_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
lean_ctor_set(v___x_2096_, 1, v___x_2094_);
return v___x_2096_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2098_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2098_, 0, lean_box(0));
lean_closure_set(v___x_2098_, 1, lean_box(0));
lean_closure_set(v___x_2098_, 2, v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2099_, lean_object* v_pre_2100_, lean_object* v_post_2101_, uint8_t v_usedLetOnly_2102_, uint8_t v_skipConstInApp_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
uint8_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_a_2113_; lean_object* v_fst_2114_; lean_object* v_snd_2115_; lean_object* v___x_2116_; 
v___x_2110_ = 0;
v___x_2111_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2112_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2111_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___x_2112_);
v_fst_2114_ = lean_ctor_get(v_a_2113_, 0);
lean_inc(v_fst_2114_);
v_snd_2115_ = lean_ctor_get(v_a_2113_, 1);
lean_inc(v_snd_2115_);
lean_dec(v_a_2113_);
v___x_2116_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2100_, v_post_2101_, v_usedLetOnly_2102_, v_skipConstInApp_2103_, v___x_2110_, v_input_2099_, v_fst_2114_, v_snd_2115_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_fst_2118_; lean_object* v_snd_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2138_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v_fst_2118_ = lean_ctor_get(v_a_2117_, 0);
lean_inc(v_fst_2118_);
v_snd_2119_ = lean_ctor_get(v_a_2117_, 1);
lean_inc(v_snd_2119_);
lean_dec(v_a_2117_);
v___x_2120_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2120_, 0, lean_box(0));
lean_closure_set(v___x_2120_, 1, lean_box(0));
lean_closure_set(v___x_2120_, 2, v_fst_2114_);
v___x_2121_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2120_, v_snd_2119_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2138_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2138_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_snd_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2136_; 
v_snd_2126_ = lean_ctor_get(v_a_2122_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_a_2122_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v_a_2122_, 0);
lean_dec(v_unused_2137_);
v___x_2128_ = v_a_2122_;
v_isShared_2129_ = v_isSharedCheck_2136_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_snd_2126_);
lean_dec(v_a_2122_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2136_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v_fst_2118_);
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_fst_2118_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_snd_2126_);
v___x_2131_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2131_);
v___x_2133_ = v___x_2124_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
else
{
lean_dec(v_fst_2114_);
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2139_, lean_object* v_pre_2140_, lean_object* v_post_2141_, lean_object* v_usedLetOnly_2142_, lean_object* v_skipConstInApp_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
uint8_t v_usedLetOnly_boxed_2150_; uint8_t v_skipConstInApp_boxed_2151_; lean_object* v_res_2152_; 
v_usedLetOnly_boxed_2150_ = lean_unbox(v_usedLetOnly_2142_);
v_skipConstInApp_boxed_2151_ = lean_unbox(v_skipConstInApp_2143_);
v_res_2152_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2139_, v_pre_2140_, v_post_2141_, v_usedLetOnly_boxed_2150_, v_skipConstInApp_boxed_2151_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___y_2162_; lean_object* v___x_2179_; uint8_t v_transparency_2180_; lean_object* v___f_2181_; lean_object* v___f_2182_; uint8_t v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2179_ = l_Lean_Meta_Context_config(v_a_2156_);
v_transparency_2180_ = lean_ctor_get_uint8(v___x_2179_, 9);
lean_dec_ref(v___x_2179_);
v___f_2181_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2182_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2183_ = 0;
v___x_2184_ = 3;
v___x_2185_ = lean_box(0);
v___x_2186_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2180_, v___x_2184_);
if (v___x_2186_ == 0)
{
lean_object* v_keyedConfig_2187_; uint8_t v_trackZetaDelta_2188_; lean_object* v_zetaDeltaSet_2189_; lean_object* v_lctx_2190_; lean_object* v_localInstances_2191_; lean_object* v_defEqCtx_x3f_2192_; lean_object* v_synthPendingDepth_2193_; lean_object* v_customCanUnfoldPredicate_x3f_2194_; uint8_t v_univApprox_2195_; uint8_t v_inTypeClassResolution_2196_; uint8_t v_cacheInferType_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_keyedConfig_2187_ = lean_ctor_get(v_a_2156_, 0);
v_trackZetaDelta_2188_ = lean_ctor_get_uint8(v_a_2156_, sizeof(void*)*7);
v_zetaDeltaSet_2189_ = lean_ctor_get(v_a_2156_, 1);
v_lctx_2190_ = lean_ctor_get(v_a_2156_, 2);
v_localInstances_2191_ = lean_ctor_get(v_a_2156_, 3);
v_defEqCtx_x3f_2192_ = lean_ctor_get(v_a_2156_, 4);
v_synthPendingDepth_2193_ = lean_ctor_get(v_a_2156_, 5);
v_customCanUnfoldPredicate_x3f_2194_ = lean_ctor_get(v_a_2156_, 6);
v_univApprox_2195_ = lean_ctor_get_uint8(v_a_2156_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2196_ = lean_ctor_get_uint8(v_a_2156_, sizeof(void*)*7 + 2);
v_cacheInferType_2197_ = lean_ctor_get_uint8(v_a_2156_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2187_);
v___x_2198_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2184_, v_keyedConfig_2187_);
lean_inc(v_customCanUnfoldPredicate_x3f_2194_);
lean_inc(v_synthPendingDepth_2193_);
lean_inc(v_defEqCtx_x3f_2192_);
lean_inc_ref(v_localInstances_2191_);
lean_inc_ref(v_lctx_2190_);
lean_inc(v_zetaDeltaSet_2189_);
v___x_2199_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
lean_ctor_set(v___x_2199_, 1, v_zetaDeltaSet_2189_);
lean_ctor_set(v___x_2199_, 2, v_lctx_2190_);
lean_ctor_set(v___x_2199_, 3, v_localInstances_2191_);
lean_ctor_set(v___x_2199_, 4, v_defEqCtx_x3f_2192_);
lean_ctor_set(v___x_2199_, 5, v_synthPendingDepth_2193_);
lean_ctor_set(v___x_2199_, 6, v_customCanUnfoldPredicate_x3f_2194_);
lean_ctor_set_uint8(v___x_2199_, sizeof(void*)*7, v_trackZetaDelta_2188_);
lean_ctor_set_uint8(v___x_2199_, sizeof(void*)*7 + 1, v_univApprox_2195_);
lean_ctor_set_uint8(v___x_2199_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2196_);
lean_ctor_set_uint8(v___x_2199_, sizeof(void*)*7 + 3, v_cacheInferType_2197_);
v___x_2200_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2155_, v___f_2182_, v___f_2181_, v___x_2183_, v___x_2183_, v___x_2185_, v___x_2199_, v_a_2157_, v_a_2158_, v_a_2159_);
lean_dec_ref_known(v___x_2199_, 7);
v___y_2162_ = v___x_2200_;
goto v___jp_2161_;
}
else
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2155_, v___f_2182_, v___f_2181_, v___x_2183_, v___x_2183_, v___x_2185_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
v___y_2162_ = v___x_2201_;
goto v___jp_2161_;
}
v___jp_2161_:
{
if (lean_obj_tag(v___y_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
v_a_2163_ = lean_ctor_get(v___y_2162_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___y_2162_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___y_2162_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___y_2162_);
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
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
v_a_2171_ = lean_ctor_get(v___y_2162_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___y_2162_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___y_2162_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___y_2162_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Meta_expandCoe(v_e_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2209_, lean_object* v_m_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2210_, v_a_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2213_, lean_object* v_m_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2213_, v_m_2214_, v_a_2215_);
lean_dec(v_a_2215_);
lean_dec_ref(v_m_2214_);
return v_res_2216_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
uint8_t v___x_2220_; 
v___x_2220_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2218_, v_x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2221_, lean_object* v_x_2222_, lean_object* v_x_2223_){
_start:
{
uint8_t v_res_2224_; lean_object* v_r_2225_; 
v_res_2224_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2221_, v_x_2222_, v_x_2223_);
lean_dec_ref(v_x_2223_);
lean_dec_ref(v_x_2222_);
v_r_2225_ = lean_box(v_res_2224_);
return v_r_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v___dummy_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg();
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
return v___x_2233_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18(lean_object* v_00_u03b1_2295_, lean_object* v_name_2296_, uint8_t v_bi_2297_, lean_object* v_type_2298_, lean_object* v_k_2299_, uint8_t v_kind_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_name_2296_, v_bi_2297_, v_type_2298_, v_k_2299_, v_kind_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___boxed(lean_object* v_00_u03b1_2309_, lean_object* v_name_2310_, lean_object* v_bi_2311_, lean_object* v_type_2312_, lean_object* v_k_2313_, lean_object* v_kind_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
uint8_t v_bi_boxed_2322_; uint8_t v_kind_boxed_2323_; lean_object* v_res_2324_; 
v_bi_boxed_2322_ = lean_unbox(v_bi_2311_);
v_kind_boxed_2323_ = lean_unbox(v_kind_2314_);
v_res_2324_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18(v_00_u03b1_2309_, v_name_2310_, v_bi_boxed_2322_, v_type_2312_, v_k_2313_, v_kind_boxed_2323_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2315_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21(lean_object* v_00_u03b1_2325_, lean_object* v_name_2326_, lean_object* v_type_2327_, lean_object* v_val_2328_, lean_object* v_k_2329_, uint8_t v_nondep_2330_, uint8_t v_kind_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(v_name_2326_, v_type_2327_, v_val_2328_, v_k_2329_, v_nondep_2330_, v_kind_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___boxed(lean_object* v_00_u03b1_2340_, lean_object* v_name_2341_, lean_object* v_type_2342_, lean_object* v_val_2343_, lean_object* v_k_2344_, lean_object* v_nondep_2345_, lean_object* v_kind_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v_nondep_boxed_2354_; uint8_t v_kind_boxed_2355_; lean_object* v_res_2356_; 
v_nondep_boxed_2354_ = lean_unbox(v_nondep_2345_);
v_kind_boxed_2355_ = lean_unbox(v_kind_2346_);
v_res_2356_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21(v_00_u03b1_2340_, v_name_2341_, v_type_2342_, v_val_2343_, v_k_2344_, v_nondep_boxed_2354_, v_kind_boxed_2355_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2347_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b1_2357_, lean_object* v_ref_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_ref_2358_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b1_2365_, lean_object* v_ref_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b1_2365_, v_ref_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
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
size_t v_x_39496__boxed_2407_; uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_x_39496__boxed_2407_ = lean_unbox_usize(v_x_2405_);
lean_dec(v_x_2405_);
v_res_2408_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2403_, v_x_2404_, v_x_39496__boxed_2407_, v_x_2406_);
lean_dec_ref(v_x_2406_);
lean_dec_ref(v_x_2404_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b2_2410_, lean_object* v_a_2411_, lean_object* v_x_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_a_2411_, v_x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b2_2414_, lean_object* v_a_2415_, lean_object* v_x_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b2_2414_, v_a_2415_, v_x_2416_);
lean_dec(v_x_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2417_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26(lean_object* v_00_u03b2_2418_, lean_object* v_a_2419_, lean_object* v_x_2420_){
_start:
{
uint8_t v___x_2421_; 
v___x_2421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(v_a_2419_, v_x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___boxed(lean_object* v_00_u03b2_2422_, lean_object* v_a_2423_, lean_object* v_x_2424_){
_start:
{
uint8_t v_res_2425_; lean_object* v_r_2426_; 
v_res_2425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26(v_00_u03b2_2422_, v_a_2423_, v_x_2424_);
lean_dec(v_x_2424_);
lean_dec_ref(v_a_2423_);
v_r_2426_ = lean_box(v_res_2425_);
return v_r_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27(lean_object* v_00_u03b2_2427_, lean_object* v_data_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_data_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28(lean_object* v_00_u03b2_2430_, lean_object* v_a_2431_, lean_object* v_b_2432_, lean_object* v_x_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28___redArg(v_a_2431_, v_b_2432_, v_x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2435_, lean_object* v_keys_2436_, lean_object* v_vals_2437_, lean_object* v_heq_2438_, lean_object* v_i_2439_, lean_object* v_k_2440_){
_start:
{
uint8_t v___x_2441_; 
v___x_2441_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2436_, v_i_2439_, v_k_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2442_, lean_object* v_keys_2443_, lean_object* v_vals_2444_, lean_object* v_heq_2445_, lean_object* v_i_2446_, lean_object* v_k_2447_){
_start:
{
uint8_t v_res_2448_; lean_object* v_r_2449_; 
v_res_2448_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2442_, v_keys_2443_, v_vals_2444_, v_heq_2445_, v_i_2446_, v_k_2447_);
lean_dec_ref(v_k_2447_);
lean_dec_ref(v_vals_2444_);
lean_dec_ref(v_keys_2443_);
v_r_2449_ = lean_box(v_res_2448_);
return v_r_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29(lean_object* v_00_u03b2_2450_, lean_object* v_i_2451_, lean_object* v_source_2452_, lean_object* v_target_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29___redArg(v_i_2451_, v_source_2452_, v_target_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30(lean_object* v_00_u03b2_2455_, lean_object* v_x_2456_, lean_object* v_x_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30___redArg(v_x_2456_, v_x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2459_, lean_object* v_decl_2460_, lean_object* v_ref_2461_){
_start:
{
lean_object* v_defValue_2463_; lean_object* v_descr_2464_; lean_object* v_deprecation_x3f_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v_defValue_2463_ = lean_ctor_get(v_decl_2460_, 0);
v_descr_2464_ = lean_ctor_get(v_decl_2460_, 1);
v_deprecation_x3f_2465_ = lean_ctor_get(v_decl_2460_, 2);
v___x_2466_ = lean_alloc_ctor(1, 0, 1);
v___x_2467_ = lean_unbox(v_defValue_2463_);
lean_ctor_set_uint8(v___x_2466_, 0, v___x_2467_);
lean_inc(v_deprecation_x3f_2465_);
lean_inc_ref(v_descr_2464_);
lean_inc_n(v_name_2459_, 2);
v___x_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2468_, 0, v_name_2459_);
lean_ctor_set(v___x_2468_, 1, v_ref_2461_);
lean_ctor_set(v___x_2468_, 2, v___x_2466_);
lean_ctor_set(v___x_2468_, 3, v_descr_2464_);
lean_ctor_set(v___x_2468_, 4, v_deprecation_x3f_2465_);
v___x_2469_ = lean_register_option(v_name_2459_, v___x_2468_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2477_; 
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v___x_2469_, 0);
lean_dec(v_unused_2478_);
v___x_2471_ = v___x_2469_;
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
else
{
lean_dec(v___x_2469_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
lean_inc(v_defValue_2463_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_name_2459_);
lean_ctor_set(v___x_2473_, 1, v_defValue_2463_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_name_2459_);
v_a_2479_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2469_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2469_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2487_, lean_object* v_decl_2488_, lean_object* v_ref_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2487_, v_decl_2488_, v_ref_2489_);
lean_dec_ref(v_decl_2488_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2506_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2507_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2508_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2509_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2506_, v___x_2507_, v___x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_ref_2518_; lean_object* v___x_2519_; lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2528_; 
v_ref_2518_ = lean_ctor_get(v___y_2515_, 2);
v___x_2519_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__7(v_msg_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2528_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2528_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2526_; 
lean_inc(v_ref_2518_);
v___x_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2524_, 0, v_ref_2518_);
lean_ctor_set(v___x_2524_, 1, v_a_2520_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set_tag(v___x_2522_, 1);
lean_ctor_set(v___x_2522_, 0, v___x_2524_);
v___x_2526_ = v___x_2522_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2535_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2544_ = l_Lean_stringToMessageData(v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2547_ = l_Lean_stringToMessageData(v___x_2546_);
return v___x_2547_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2550_ = l_Lean_stringToMessageData(v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2551_, lean_object* v_expectedType_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v___x_2558_; 
lean_inc(v_a_2556_);
lean_inc_ref(v_a_2555_);
lean_inc(v_a_2554_);
lean_inc_ref(v_a_2553_);
lean_inc_ref(v_expr_2551_);
v___x_2558_ = lean_infer_type(v_expr_2551_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc_n(v_a_2559_, 2);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = l_Lean_Meta_getLevel(v_a_2559_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2562_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2560_, 1);
lean_inc_ref(v_expectedType_2552_);
v___x_2562_ = l_Lean_Meta_getLevel(v_expectedType_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2565_ = lean_box(0);
v___x_2566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_a_2563_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v_a_2561_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
lean_inc_ref(v___x_2567_);
v___x_2568_ = l_Lean_mkConst(v___x_2564_, v___x_2567_);
v___x_2569_ = lean_unsigned_to_nat(3u);
v___x_2570_ = lean_mk_empty_array_with_capacity(v___x_2569_);
lean_inc(v_a_2559_);
v___x_2571_ = lean_array_push(v___x_2570_, v_a_2559_);
lean_inc_ref(v_expr_2551_);
v___x_2572_ = lean_array_push(v___x_2571_, v_expr_2551_);
lean_inc_ref(v_expectedType_2552_);
v___x_2573_ = lean_array_push(v___x_2572_, v_expectedType_2552_);
v___x_2574_ = l_Lean_mkAppN(v___x_2568_, v___x_2573_);
lean_dec_ref(v___x_2573_);
v___x_2575_ = lean_box(0);
v___x_2576_ = l_Lean_Meta_trySynthInstance(v___x_2574_, v___x_2575_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2674_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2674_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2674_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
switch(lean_obj_tag(v_a_2577_))
{
case 0:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
lean_dec_ref_known(v___x_2567_, 2);
lean_dec(v_a_2559_);
lean_dec_ref(v_expectedType_2552_);
lean_dec_ref(v_expr_2551_);
v___x_2581_ = lean_box(0);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
case 1:
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2669_; 
lean_del_object(v___x_2579_);
v_a_2585_ = lean_ctor_get(v_a_2577_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_a_2577_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2587_ = v_a_2577_;
v_isShared_2588_ = v_isSharedCheck_2669_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v_a_2577_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2669_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2589_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2590_ = l_Lean_mkConst(v___x_2589_, v___x_2567_);
v___x_2591_ = lean_unsigned_to_nat(4u);
v___x_2592_ = lean_mk_empty_array_with_capacity(v___x_2591_);
v___x_2593_ = lean_array_push(v___x_2592_, v_a_2559_);
lean_inc_ref(v_expr_2551_);
v___x_2594_ = lean_array_push(v___x_2593_, v_expr_2551_);
lean_inc_ref(v_expectedType_2552_);
v___x_2595_ = lean_array_push(v___x_2594_, v_expectedType_2552_);
v___x_2596_ = lean_array_push(v___x_2595_, v_a_2585_);
v___x_2597_ = l_Lean_mkAppN(v___x_2590_, v___x_2596_);
lean_dec_ref(v___x_2596_);
v___x_2598_ = l_Lean_Meta_expandCoe(v___x_2597_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2660_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2660_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2660_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v_fst_2610_; lean_object* v___x_2611_; 
v_fst_2610_ = lean_ctor_get(v_a_2599_, 0);
lean_inc(v_a_2556_);
lean_inc_ref(v_a_2555_);
lean_inc(v_a_2554_);
lean_inc_ref(v_a_2553_);
lean_inc(v_fst_2610_);
v___x_2611_ = lean_infer_type(v_fst_2610_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2613_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
lean_inc_ref(v_expectedType_2552_);
v___x_2613_ = l_Lean_Meta_isExprDefEq(v_a_2612_, v_expectedType_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; uint8_t v___x_2615_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2613_, 1);
v___x_2615_ = lean_unbox(v_a_2614_);
lean_dec(v_a_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2641_; 
lean_inc(v_fst_2610_);
lean_del_object(v___x_2601_);
lean_del_object(v___x_2587_);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_a_2599_);
if (v_isSharedCheck_2641_ == 0)
{
lean_object* v_unused_2642_; lean_object* v_unused_2643_; 
v_unused_2642_ = lean_ctor_get(v_a_2599_, 1);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v_a_2599_, 0);
lean_dec(v_unused_2643_);
v___x_2617_ = v_a_2599_;
v_isShared_2618_ = v_isSharedCheck_2641_;
goto v_resetjp_2616_;
}
else
{
lean_dec(v_a_2599_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2641_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2619_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2620_ = l_Lean_indentExpr(v_expr_2551_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 7);
lean_ctor_set(v___x_2617_, 1, v___x_2620_);
lean_ctor_set(v___x_2617_, 0, v___x_2619_);
v___x_2622_ = v___x_2617_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
v___x_2623_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = l_Lean_indentExpr(v_expectedType_2552_);
v___x_2626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2624_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2626_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = l_Lean_indentExpr(v_fst_2610_);
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2630_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
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
}
}
else
{
lean_dec_ref(v_expectedType_2552_);
lean_dec_ref(v_expr_2551_);
goto v___jp_2603_;
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_del_object(v___x_2601_);
lean_dec(v_a_2599_);
lean_del_object(v___x_2587_);
lean_dec_ref(v_expectedType_2552_);
lean_dec_ref(v_expr_2551_);
v_a_2644_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2613_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2613_);
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
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_del_object(v___x_2601_);
lean_dec(v_a_2599_);
lean_del_object(v___x_2587_);
lean_dec_ref(v_expectedType_2552_);
lean_dec_ref(v_expr_2551_);
v_a_2652_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2611_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2611_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
v___jp_2603_:
{
lean_object* v___x_2605_; 
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 0, v_a_2599_);
v___x_2605_ = v___x_2587_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2599_);
v___x_2605_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2607_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2605_);
v___x_2607_ = v___x_2601_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_del_object(v___x_2587_);
lean_dec_ref(v_expectedType_2552_);
lean_dec_ref(v_expr_2551_);
v_a_2661_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2598_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2598_);
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
}
default: 
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
lean_dec_ref_known(v___x_2567_, 2);
lean_dec(v_a_2559_);
lean_dec_ref(v_expectedType_2552_);
lean_dec_ref(v_expr_2551_);
v___x_2670_ = lean_box(2);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2670_);
v___x_2672_ = v___x_2579_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
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
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec_ref_known(v___x_2567_, 2);
lean_dec(v_a_2559_);
lean_dec_ref(v_expectedType_2552_);
lean_dec_ref(v_expr_2551_);
v_a_2675_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2576_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2576_);
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
lean_dec(v_a_2561_);
lean_dec(v_a_2559_);
lean_dec_ref(v_expectedType_2552_);
lean_dec_ref(v_expr_2551_);
v_a_2683_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2562_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2562_);
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
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_a_2559_);
lean_dec_ref(v_expectedType_2552_);
lean_dec_ref(v_expr_2551_);
v_a_2691_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2560_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2560_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec_ref(v_expectedType_2552_);
lean_dec_ref(v_expr_2551_);
v_a_2699_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2558_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2558_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2707_, lean_object* v_expectedType_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2707_, v_expectedType_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2715_, lean_object* v_msg_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2723_, lean_object* v_msg_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2723_, v_msg_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2731_, lean_object* v_expectedType_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2731_, v_expectedType_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2763_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2763_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2763_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
switch(lean_obj_tag(v_a_2739_))
{
case 0:
{
lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2743_ = lean_box(0);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2743_);
v___x_2745_ = v___x_2741_;
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
case 1:
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2758_; 
v_a_2747_ = lean_ctor_get(v_a_2739_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_a_2739_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2749_ = v_a_2739_;
v_isShared_2750_ = v_isSharedCheck_2758_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v_a_2739_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2758_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_fst_2751_; lean_object* v___x_2753_; 
v_fst_2751_ = lean_ctor_get(v_a_2747_, 0);
lean_inc(v_fst_2751_);
lean_dec(v_a_2747_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v_fst_2751_);
v___x_2753_ = v___x_2749_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_fst_2751_);
v___x_2753_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2755_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2753_);
v___x_2755_ = v___x_2741_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
default: 
{
lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2759_ = lean_box(2);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2759_);
v___x_2761_ = v___x_2741_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
v_a_2764_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2738_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2738_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2772_, lean_object* v_expectedType_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2772_, v_expectedType_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
return v_res_2779_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2788_ = l_Lean_stringToMessageData(v___x_2787_);
return v___x_2788_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2791_ = l_Lean_stringToMessageData(v___x_2790_);
return v___x_2791_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2794_ = l_Lean_stringToMessageData(v___x_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; 
lean_inc(v_a_2799_);
lean_inc_ref(v_a_2798_);
lean_inc(v_a_2797_);
lean_inc_ref(v_a_2796_);
lean_inc_ref(v_expr_2795_);
v___x_2801_ = lean_infer_type(v_expr_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2803_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc_n(v_a_2802_, 2);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2803_ = l_Lean_Meta_getLevel(v_a_2802_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2805_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v___x_2805_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc_n(v_a_2806_, 2);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = l_Lean_mkSort(v_a_2806_);
lean_inc(v_a_2802_);
v___x_2808_ = l_Lean_mkArrow(v_a_2802_, v___x_2807_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_a_2809_);
v___x_2811_ = 0;
v___x_2812_ = lean_box(0);
v___x_2813_ = l_Lean_Meta_mkFreshExprMVar(v___x_2810_, v___x_2811_, v___x_2812_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc_n(v_a_2814_, 2);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2815_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2817_, 0, v_a_2806_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2818_, 0, v_a_2804_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
lean_inc_ref(v___x_2818_);
v___x_2819_ = l_Lean_Expr_const___override(v___x_2815_, v___x_2818_);
lean_inc(v_a_2802_);
v___x_2820_ = l_Lean_mkAppB(v___x_2819_, v_a_2802_, v_a_2814_);
v___x_2821_ = lean_box(0);
v___x_2822_ = l_Lean_Meta_trySynthInstance(v___x_2820_, v___x_2821_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2909_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2909_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2909_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
if (lean_obj_tag(v_a_2823_) == 1)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2905_; 
lean_del_object(v___x_2825_);
v_a_2827_ = lean_ctor_get(v_a_2823_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_a_2823_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2829_ = v_a_2823_;
v_isShared_2830_ = v_isSharedCheck_2905_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v_a_2823_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2905_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2831_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2832_ = l_Lean_Expr_const___override(v___x_2831_, v___x_2818_);
lean_inc_ref(v_expr_2795_);
lean_inc(v_a_2827_);
v___x_2833_ = l_Lean_mkApp4(v___x_2832_, v_a_2802_, v_a_2814_, v_a_2827_, v_expr_2795_);
v___x_2834_ = l_Lean_Meta_expandCoe(v___x_2833_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2896_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2837_ = v___x_2834_;
v_isShared_2838_ = v_isSharedCheck_2896_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2896_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v_fst_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2894_; 
v_fst_2839_ = lean_ctor_get(v_a_2835_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_a_2835_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; 
v_unused_2895_ = lean_ctor_get(v_a_2835_, 1);
lean_dec(v_unused_2895_);
v___x_2841_ = v_a_2835_;
v_isShared_2842_ = v_isSharedCheck_2894_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_fst_2839_);
lean_dec(v_a_2835_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2894_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2850_; 
lean_inc(v_a_2799_);
lean_inc_ref(v_a_2798_);
lean_inc(v_a_2797_);
lean_inc_ref(v_a_2796_);
lean_inc(v_fst_2839_);
v___x_2850_ = lean_infer_type(v_fst_2839_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
lean_inc(v_a_2799_);
lean_inc_ref(v_a_2798_);
lean_inc(v_a_2797_);
lean_inc_ref(v_a_2796_);
v___x_2852_ = lean_whnf(v_a_2851_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; uint8_t v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l_Lean_Expr_isForall(v_a_2853_);
lean_dec(v_a_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2858_; 
lean_del_object(v___x_2837_);
lean_del_object(v___x_2829_);
v___x_2855_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2856_ = l_Lean_indentExpr(v_expr_2795_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 7);
lean_ctor_set(v___x_2841_, 1, v___x_2856_);
lean_ctor_set(v___x_2841_, 0, v___x_2855_);
v___x_2858_ = v___x_2841_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
v___x_2859_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = l_Lean_indentExpr(v_fst_2839_);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2864_ = l_Lean_indentExpr(v_a_2827_);
v___x_2865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = l_Lean_MessageData_hint_x27(v___x_2865_);
v___x_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2862_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2867_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_del_object(v___x_2841_);
lean_dec(v_a_2827_);
lean_dec_ref(v_expr_2795_);
goto v___jp_2843_;
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_del_object(v___x_2841_);
lean_dec(v_fst_2839_);
lean_del_object(v___x_2837_);
lean_del_object(v___x_2829_);
lean_dec(v_a_2827_);
lean_dec_ref(v_expr_2795_);
v_a_2878_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2852_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2852_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_del_object(v___x_2841_);
lean_dec(v_fst_2839_);
lean_del_object(v___x_2837_);
lean_del_object(v___x_2829_);
lean_dec(v_a_2827_);
lean_dec_ref(v_expr_2795_);
v_a_2886_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2850_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2850_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
v___jp_2843_:
{
lean_object* v___x_2845_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v_fst_2839_);
v___x_2845_ = v___x_2829_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_fst_2839_);
v___x_2845_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2847_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2845_);
v___x_2847_ = v___x_2837_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
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
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_del_object(v___x_2829_);
lean_dec(v_a_2827_);
lean_dec_ref(v_expr_2795_);
v_a_2897_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2834_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2834_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
else
{
lean_object* v___x_2907_; 
lean_dec(v_a_2823_);
lean_dec_ref_known(v___x_2818_, 2);
lean_dec(v_a_2814_);
lean_dec(v_a_2802_);
lean_dec_ref(v_expr_2795_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_2821_);
v___x_2907_ = v___x_2825_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2821_);
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
lean_dec_ref_known(v___x_2818_, 2);
lean_dec(v_a_2814_);
lean_dec(v_a_2802_);
lean_dec_ref(v_expr_2795_);
v_a_2910_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2822_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2822_);
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
lean_dec(v_a_2806_);
lean_dec(v_a_2804_);
lean_dec(v_a_2802_);
lean_dec_ref(v_expr_2795_);
v_a_2918_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2813_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2813_);
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
lean_dec(v_a_2806_);
lean_dec(v_a_2804_);
lean_dec(v_a_2802_);
lean_dec_ref(v_expr_2795_);
v_a_2926_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2808_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2808_);
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
lean_dec(v_a_2804_);
lean_dec(v_a_2802_);
lean_dec_ref(v_expr_2795_);
v_a_2934_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2805_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2805_);
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
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v_a_2802_);
lean_dec_ref(v_expr_2795_);
v_a_2942_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2803_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2803_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec_ref(v_expr_2795_);
v_a_2950_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2801_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2801_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
return v_res_2964_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2973_ = l_Lean_stringToMessageData(v___x_2972_);
return v___x_2973_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2976_ = l_Lean_stringToMessageData(v___x_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v___x_2983_; 
lean_inc(v_a_2981_);
lean_inc_ref(v_a_2980_);
lean_inc(v_a_2979_);
lean_inc_ref(v_a_2978_);
lean_inc_ref(v_expr_2977_);
v___x_2983_ = lean_infer_type(v_expr_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc_n(v_a_2984_, 2);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = l_Lean_Meta_getLevel(v_a_2984_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v___x_2987_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc_n(v_a_2988_, 2);
lean_dec_ref_known(v___x_2987_, 1);
v___x_2989_ = l_Lean_mkSort(v_a_2988_);
v___x_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
v___x_2991_ = 0;
v___x_2992_ = lean_box(0);
v___x_2993_ = l_Lean_Meta_mkFreshExprMVar(v___x_2990_, v___x_2991_, v___x_2992_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc_n(v_a_2994_, 2);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_2996_ = lean_box(0);
v___x_2997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2997_, 0, v_a_2988_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2998_, 0, v_a_2986_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
lean_inc_ref(v___x_2998_);
v___x_2999_ = l_Lean_Expr_const___override(v___x_2995_, v___x_2998_);
lean_inc(v_a_2984_);
v___x_3000_ = l_Lean_mkAppB(v___x_2999_, v_a_2984_, v_a_2994_);
v___x_3001_ = lean_box(0);
v___x_3002_ = l_Lean_Meta_trySynthInstance(v___x_3000_, v___x_3001_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3089_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3089_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3089_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
if (lean_obj_tag(v_a_3003_) == 1)
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3085_; 
lean_del_object(v___x_3005_);
v_a_3007_ = lean_ctor_get(v_a_3003_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_a_3003_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3009_ = v_a_3003_;
v_isShared_3010_ = v_isSharedCheck_3085_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v_a_3003_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3085_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3011_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_3012_ = l_Lean_Expr_const___override(v___x_3011_, v___x_2998_);
lean_inc_ref(v_expr_2977_);
lean_inc(v_a_3007_);
v___x_3013_ = l_Lean_mkApp4(v___x_3012_, v_a_2984_, v_a_2994_, v_a_3007_, v_expr_2977_);
v___x_3014_ = l_Lean_Meta_expandCoe(v___x_3013_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3076_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3076_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3076_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v_fst_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3074_; 
v_fst_3019_ = lean_ctor_get(v_a_3015_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_a_3015_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v_a_3015_, 1);
lean_dec(v_unused_3075_);
v___x_3021_ = v_a_3015_;
v_isShared_3022_ = v_isSharedCheck_3074_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_fst_3019_);
lean_dec(v_a_3015_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3074_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3030_; 
lean_inc(v_a_2981_);
lean_inc_ref(v_a_2980_);
lean_inc(v_a_2979_);
lean_inc_ref(v_a_2978_);
lean_inc(v_fst_3019_);
v___x_3030_ = lean_infer_type(v_fst_3019_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
lean_inc(v_a_2981_);
lean_inc_ref(v_a_2980_);
lean_inc(v_a_2979_);
lean_inc_ref(v_a_2978_);
v___x_3032_ = lean_whnf(v_a_3031_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; uint8_t v___x_3034_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = l_Lean_Expr_isSort(v_a_3033_);
lean_dec(v_a_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
lean_del_object(v___x_3017_);
lean_del_object(v___x_3009_);
v___x_3035_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3036_ = l_Lean_indentExpr(v_expr_2977_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set_tag(v___x_3021_, 7);
lean_ctor_set(v___x_3021_, 1, v___x_3036_);
lean_ctor_set(v___x_3021_, 0, v___x_3035_);
v___x_3038_ = v___x_3021_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
v___x_3039_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3038_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = l_Lean_indentExpr(v_fst_3019_);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3044_ = l_Lean_indentExpr(v_a_3007_);
v___x_3045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = l_Lean_MessageData_hint_x27(v___x_3045_);
v___x_3047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3042_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3047_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_del_object(v___x_3021_);
lean_dec(v_a_3007_);
lean_dec_ref(v_expr_2977_);
goto v___jp_3023_;
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_del_object(v___x_3021_);
lean_dec(v_fst_3019_);
lean_del_object(v___x_3017_);
lean_del_object(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec_ref(v_expr_2977_);
v_a_3058_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3032_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3032_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_del_object(v___x_3021_);
lean_dec(v_fst_3019_);
lean_del_object(v___x_3017_);
lean_del_object(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec_ref(v_expr_2977_);
v_a_3066_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3030_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3030_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
v___jp_3023_:
{
lean_object* v___x_3025_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v_fst_3019_);
v___x_3025_ = v___x_3009_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_fst_3019_);
v___x_3025_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3027_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3025_);
v___x_3027_ = v___x_3017_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3025_);
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
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_del_object(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec_ref(v_expr_2977_);
v_a_3077_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3014_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3014_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
else
{
lean_object* v___x_3087_; 
lean_dec(v_a_3003_);
lean_dec_ref_known(v___x_2998_, 2);
lean_dec(v_a_2994_);
lean_dec(v_a_2984_);
lean_dec_ref(v_expr_2977_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3001_);
v___x_3087_ = v___x_3005_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3001_);
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
lean_dec_ref_known(v___x_2998_, 2);
lean_dec(v_a_2994_);
lean_dec(v_a_2984_);
lean_dec_ref(v_expr_2977_);
v_a_3090_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3002_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3002_);
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
lean_dec(v_a_2988_);
lean_dec(v_a_2986_);
lean_dec(v_a_2984_);
lean_dec_ref(v_expr_2977_);
v_a_3098_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_2993_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_2993_);
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
lean_dec(v_a_2986_);
lean_dec(v_a_2984_);
lean_dec_ref(v_expr_2977_);
v_a_3106_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_2987_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_2987_);
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
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec(v_a_2984_);
lean_dec_ref(v_expr_2977_);
v_a_3114_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_2985_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_2985_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec_ref(v_expr_2977_);
v_a_3122_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_2983_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_2983_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3137_, lean_object* v___y_3138_){
_start:
{
uint8_t v___x_3140_; 
v___x_3140_ = l_Lean_Expr_hasMVar(v_e_3137_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v_e_3137_);
return v___x_3141_;
}
else
{
lean_object* v___x_3142_; lean_object* v_mctx_3143_; lean_object* v___x_3144_; lean_object* v_fst_3145_; lean_object* v_snd_3146_; lean_object* v___x_3147_; lean_object* v_cache_3148_; lean_object* v_zetaDeltaFVarIds_3149_; lean_object* v_postponed_3150_; lean_object* v_diag_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3160_; 
v___x_3142_ = lean_st_ref_get(v___y_3138_);
v_mctx_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc_ref(v_mctx_3143_);
lean_dec(v___x_3142_);
v___x_3144_ = l_Lean_instantiateMVarsCore(v_mctx_3143_, v_e_3137_);
v_fst_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_fst_3145_);
v_snd_3146_ = lean_ctor_get(v___x_3144_, 1);
lean_inc(v_snd_3146_);
lean_dec_ref(v___x_3144_);
v___x_3147_ = lean_st_ref_take(v___y_3138_);
v_cache_3148_ = lean_ctor_get(v___x_3147_, 1);
v_zetaDeltaFVarIds_3149_ = lean_ctor_get(v___x_3147_, 2);
v_postponed_3150_ = lean_ctor_get(v___x_3147_, 3);
v_diag_3151_ = lean_ctor_get(v___x_3147_, 4);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v___x_3147_, 0);
lean_dec(v_unused_3161_);
v___x_3153_ = v___x_3147_;
v_isShared_3154_ = v_isSharedCheck_3160_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_diag_3151_);
lean_inc(v_postponed_3150_);
lean_inc(v_zetaDeltaFVarIds_3149_);
lean_inc(v_cache_3148_);
lean_dec(v___x_3147_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3160_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v_snd_3146_);
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_snd_3146_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_cache_3148_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_zetaDeltaFVarIds_3149_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_postponed_3150_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_diag_3151_);
v___x_3156_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_st_ref_put(v___y_3138_, v___x_3156_);
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v_fst_3145_);
return v___x_3158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3162_, v___y_3163_);
lean_dec(v___y_3163_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3166_, v___y_3168_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v___y_3187_; lean_object* v___x_3226_; uint8_t v_transparency_3227_; uint8_t v___x_3228_; uint8_t v___x_3229_; 
v___x_3226_ = l_Lean_Meta_Context_config(v_a_3181_);
v_transparency_3227_ = lean_ctor_get_uint8(v___x_3226_, 9);
lean_dec_ref(v___x_3226_);
v___x_3228_ = 2;
v___x_3229_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3227_, v___x_3228_);
if (v___x_3229_ == 0)
{
lean_object* v_keyedConfig_3230_; uint8_t v_trackZetaDelta_3231_; lean_object* v_zetaDeltaSet_3232_; lean_object* v_lctx_3233_; lean_object* v_localInstances_3234_; lean_object* v_defEqCtx_x3f_3235_; lean_object* v_synthPendingDepth_3236_; lean_object* v_customCanUnfoldPredicate_x3f_3237_; uint8_t v_univApprox_3238_; uint8_t v_inTypeClassResolution_3239_; uint8_t v_cacheInferType_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v_keyedConfig_3230_ = lean_ctor_get(v_a_3181_, 0);
v_trackZetaDelta_3231_ = lean_ctor_get_uint8(v_a_3181_, sizeof(void*)*7);
v_zetaDeltaSet_3232_ = lean_ctor_get(v_a_3181_, 1);
v_lctx_3233_ = lean_ctor_get(v_a_3181_, 2);
v_localInstances_3234_ = lean_ctor_get(v_a_3181_, 3);
v_defEqCtx_x3f_3235_ = lean_ctor_get(v_a_3181_, 4);
v_synthPendingDepth_3236_ = lean_ctor_get(v_a_3181_, 5);
v_customCanUnfoldPredicate_x3f_3237_ = lean_ctor_get(v_a_3181_, 6);
v_univApprox_3238_ = lean_ctor_get_uint8(v_a_3181_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3239_ = lean_ctor_get_uint8(v_a_3181_, sizeof(void*)*7 + 2);
v_cacheInferType_3240_ = lean_ctor_get_uint8(v_a_3181_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3230_);
v___x_3241_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3228_, v_keyedConfig_3230_);
lean_inc(v_customCanUnfoldPredicate_x3f_3237_);
lean_inc(v_synthPendingDepth_3236_);
lean_inc(v_defEqCtx_x3f_3235_);
lean_inc_ref(v_localInstances_3234_);
lean_inc_ref(v_lctx_3233_);
lean_inc(v_zetaDeltaSet_3232_);
v___x_3242_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
lean_ctor_set(v___x_3242_, 1, v_zetaDeltaSet_3232_);
lean_ctor_set(v___x_3242_, 2, v_lctx_3233_);
lean_ctor_set(v___x_3242_, 3, v_localInstances_3234_);
lean_ctor_set(v___x_3242_, 4, v_defEqCtx_x3f_3235_);
lean_ctor_set(v___x_3242_, 5, v_synthPendingDepth_3236_);
lean_ctor_set(v___x_3242_, 6, v_customCanUnfoldPredicate_x3f_3237_);
lean_ctor_set_uint8(v___x_3242_, sizeof(void*)*7, v_trackZetaDelta_3231_);
lean_ctor_set_uint8(v___x_3242_, sizeof(void*)*7 + 1, v_univApprox_3238_);
lean_ctor_set_uint8(v___x_3242_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3239_);
lean_ctor_set_uint8(v___x_3242_, sizeof(void*)*7 + 3, v_cacheInferType_3240_);
lean_inc(v_a_3184_);
lean_inc_ref(v_a_3183_);
lean_inc(v_a_3182_);
v___x_3243_ = lean_whnf(v_type_3180_, v___x_3242_, v_a_3182_, v_a_3183_, v_a_3184_);
v___y_3187_ = v___x_3243_;
goto v___jp_3186_;
}
else
{
lean_object* v___x_3244_; 
lean_inc(v_a_3184_);
lean_inc_ref(v_a_3183_);
lean_inc(v_a_3182_);
lean_inc_ref(v_a_3181_);
v___x_3244_ = lean_whnf(v_type_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
v___y_3187_ = v___x_3244_;
goto v___jp_3186_;
}
v___jp_3186_:
{
if (lean_obj_tag(v___y_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3217_; 
v_a_3188_ = lean_ctor_get(v___y_3187_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___y_3187_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3190_ = v___y_3187_;
v_isShared_3191_ = v_isSharedCheck_3217_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___y_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3217_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
if (lean_obj_tag(v_a_3188_) == 5)
{
lean_object* v_fn_3192_; lean_object* v_arg_3193_; lean_object* v___x_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3212_; 
lean_del_object(v___x_3190_);
v_fn_3192_ = lean_ctor_get(v_a_3188_, 0);
lean_inc_ref(v_fn_3192_);
v_arg_3193_ = lean_ctor_get(v_a_3188_, 1);
lean_inc_ref(v_arg_3193_);
lean_dec_ref_known(v_a_3188_, 2);
v___x_3194_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3192_, v_a_3182_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3212_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3212_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3211_; 
v___x_3199_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3193_, v_a_3182_);
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3211_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3211_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3206_; 
v___x_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3204_, 0, v_a_3195_);
lean_ctor_set(v___x_3204_, 1, v_a_3200_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set_tag(v___x_3197_, 1);
lean_ctor_set(v___x_3197_, 0, v___x_3204_);
v___x_3206_ = v___x_3197_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3208_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___x_3206_);
v___x_3208_ = v___x_3202_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
}
else
{
lean_object* v___x_3213_; lean_object* v___x_3215_; 
lean_dec(v_a_3188_);
v___x_3213_ = lean_box(0);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 0, v___x_3213_);
v___x_3215_ = v___x_3190_;
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
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
v_a_3218_ = lean_ctor_get(v___y_3187_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___y_3187_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___y_3187_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___y_3187_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Lean_Meta_isTypeApp_x3f(v_type_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_Meta_isTypeApp_x3f(v_type_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3294_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3294_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3294_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
if (lean_obj_tag(v_a_3259_) == 1)
{
lean_object* v_val_3263_; lean_object* v_fst_3264_; lean_object* v___x_3265_; 
lean_del_object(v___x_3261_);
v_val_3263_ = lean_ctor_get(v_a_3259_, 0);
lean_inc(v_val_3263_);
lean_dec_ref_known(v_a_3259_, 1);
v_fst_3264_ = lean_ctor_get(v_val_3263_, 0);
lean_inc(v_fst_3264_);
lean_dec(v_val_3263_);
v___x_3265_ = l_Lean_Meta_isMonad_x3f(v_fst_3264_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3280_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3280_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3280_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
if (lean_obj_tag(v_a_3266_) == 0)
{
uint8_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3270_ = 0;
v___x_3271_ = lean_box(v___x_3270_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3271_);
v___x_3273_ = v___x_3268_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
else
{
uint8_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
lean_dec_ref_known(v_a_3266_, 1);
v___x_3275_ = 1;
v___x_3276_ = lean_box(v___x_3275_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3276_);
v___x_3278_ = v___x_3268_;
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
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
v_a_3281_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3265_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3265_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
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
uint8_t v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; 
lean_dec(v_a_3259_);
v___x_3289_ = 0;
v___x_3290_ = lean_box(v___x_3289_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3290_);
v___x_3292_ = v___x_3261_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3290_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
v_a_3295_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3258_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3258_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_Meta_isMonadApp(v_type_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
return v_res_3309_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3310_, lean_object* v_opt_3311_){
_start:
{
lean_object* v_name_3312_; lean_object* v_defValue_3313_; lean_object* v_map_3314_; lean_object* v___x_3315_; 
v_name_3312_ = lean_ctor_get(v_opt_3311_, 0);
v_defValue_3313_ = lean_ctor_get(v_opt_3311_, 1);
v_map_3314_ = lean_ctor_get(v_opts_3310_, 0);
v___x_3315_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3314_, v_name_3312_);
if (lean_obj_tag(v___x_3315_) == 0)
{
uint8_t v___x_3316_; 
v___x_3316_ = lean_unbox(v_defValue_3313_);
return v___x_3316_;
}
else
{
lean_object* v_val_3317_; 
v_val_3317_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_val_3317_);
lean_dec_ref_known(v___x_3315_, 1);
if (lean_obj_tag(v_val_3317_) == 1)
{
uint8_t v_v_3318_; 
v_v_3318_ = lean_ctor_get_uint8(v_val_3317_, 0);
lean_dec_ref_known(v_val_3317_, 0);
return v_v_3318_;
}
else
{
uint8_t v___x_3319_; 
lean_dec(v_val_3317_);
v___x_3319_ = lean_unbox(v_defValue_3313_);
return v___x_3319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3320_, lean_object* v_opt_3321_){
_start:
{
uint8_t v_res_3322_; lean_object* v_r_3323_; 
v_res_3322_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3320_, v_opt_3321_);
lean_dec_ref(v_opt_3321_);
lean_dec_ref(v_opts_3320_);
v_r_3323_ = lean_box(v_res_3322_);
return v_r_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v_x_3334_);
return v_res_3340_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = l_Lean_mkBVar(v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3363_, lean_object* v_expectedType_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_a_3371_; lean_object* v___y_3379_; lean_object* v___x_3389_; lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3793_; 
v___x_3389_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3364_, v_a_3366_);
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3392_ = v___x_3389_;
v_isShared_3393_ = v_isSharedCheck_3793_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3389_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3793_;
goto v_resetjp_3391_;
}
v___jp_3370_:
{
uint8_t v___x_3372_; 
v___x_3372_ = l_Lean_Exception_isInterrupt(v_a_3371_);
if (v___x_3372_ == 0)
{
uint8_t v___x_3373_; 
lean_inc_ref(v_a_3371_);
v___x_3373_ = l_Lean_Exception_isRuntime(v_a_3371_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec_ref(v_a_3371_);
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
return v___x_3375_;
}
else
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3376_, 0, v_a_3371_);
return v___x_3376_;
}
}
else
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3377_, 0, v_a_3371_);
return v___x_3377_;
}
}
v___jp_3378_:
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3388_; 
v_a_3380_ = lean_ctor_get(v___y_3379_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___y_3379_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3382_ = v___y_3379_;
v_isShared_3383_ = v_isSharedCheck_3388_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___y_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3388_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v_a_3384_; lean_object* v___x_3386_; 
v_a_3384_ = lean_ctor_get(v_a_3380_, 0);
lean_inc(v_a_3384_);
lean_dec(v_a_3380_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v_a_3384_);
v___x_3386_ = v___x_3382_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3384_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; 
lean_inc(v_a_3368_);
lean_inc_ref(v_a_3367_);
lean_inc(v_a_3366_);
lean_inc_ref(v_a_3365_);
lean_inc_ref(v_e_3363_);
v___x_3394_ = lean_infer_type(v_e_3363_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3396_; lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3784_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v___x_3396_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3395_, v_a_3366_);
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3784_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3784_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3401_; 
lean_inc(v_a_3390_);
v___x_3401_ = l_Lean_Meta_isTypeApp_x3f(v_a_3390_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3775_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3775_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3775_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
if (lean_obj_tag(v_a_3402_) == 1)
{
lean_object* v_val_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3770_; 
lean_del_object(v___x_3404_);
v_val_3406_ = lean_ctor_get(v_a_3402_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v_a_3402_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3408_ = v_a_3402_;
v_isShared_3409_ = v_isSharedCheck_3770_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_val_3406_);
lean_dec(v_a_3402_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3770_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3769_; 
v_fst_3410_ = lean_ctor_get(v_val_3406_, 0);
v_snd_3411_ = lean_ctor_get(v_val_3406_, 1);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_val_3406_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3413_ = v_val_3406_;
v_isShared_3414_ = v_isSharedCheck_3769_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_snd_3411_);
lean_inc(v_fst_3410_);
lean_dec(v_val_3406_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3769_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; 
lean_inc(v_a_3397_);
v___x_3415_ = l_Lean_Meta_isTypeApp_x3f(v_a_3397_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3760_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3760_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3760_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
if (lean_obj_tag(v_a_3416_) == 1)
{
lean_object* v_val_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3755_; 
lean_del_object(v___x_3418_);
v_val_3420_ = lean_ctor_get(v_a_3416_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3422_ = v_a_3416_;
v_isShared_3423_ = v_isSharedCheck_3755_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_val_3420_);
lean_dec(v_a_3416_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3755_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v_fst_3424_; lean_object* v_snd_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3754_; 
v_fst_3424_ = lean_ctor_get(v_val_3420_, 0);
v_snd_3425_ = lean_ctor_get(v_val_3420_, 1);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_val_3420_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3427_ = v_val_3420_;
v_isShared_3428_ = v_isSharedCheck_3754_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_snd_3425_);
lean_inc(v_fst_3424_);
lean_dec(v_val_3420_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3754_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_Meta_saveState___redArg(v_a_3366_, v_a_3368_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3431_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
lean_inc(v_fst_3410_);
lean_inc(v_fst_3424_);
v___x_3431_ = l_Lean_Meta_isExprDefEq(v_fst_3424_, v_fst_3410_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3737_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3737_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3737_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
uint8_t v___x_3436_; 
v___x_3436_ = lean_unbox(v_a_3432_);
lean_dec(v_a_3432_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
lean_dec(v_a_3430_);
lean_del_object(v___x_3408_);
lean_del_object(v___x_3399_);
lean_del_object(v___x_3392_);
v___x_3437_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3367_);
v___x_3438_ = l_Lean_Meta_autoLift;
v___x_3439_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v___x_3437_, v___x_3438_);
lean_dec_ref(v___x_3437_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v___x_3440_ = lean_box(0);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v___x_3440_);
v___x_3442_ = v___x_3434_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
else
{
lean_object* v___x_3444_; 
lean_del_object(v___x_3434_);
lean_inc(v_a_3368_);
lean_inc_ref(v_a_3367_);
lean_inc(v_a_3366_);
lean_inc_ref(v_a_3365_);
lean_inc(v_fst_3424_);
v___x_3444_ = lean_infer_type(v_fst_3424_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref_known(v___x_3444_, 1);
lean_inc(v_a_3368_);
lean_inc_ref(v_a_3367_);
lean_inc(v_a_3366_);
lean_inc_ref(v_a_3365_);
v___x_3446_ = lean_whnf(v_a_3445_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
if (lean_obj_tag(v_a_3447_) == 7)
{
lean_object* v_binderType_3448_; 
v_binderType_3448_ = lean_ctor_get(v_a_3447_, 1);
if (lean_obj_tag(v_binderType_3448_) == 3)
{
lean_object* v_body_3449_; 
v_body_3449_ = lean_ctor_get(v_a_3447_, 2);
if (lean_obj_tag(v_body_3449_) == 3)
{
lean_object* v_u_3450_; lean_object* v_u_3451_; lean_object* v___x_3452_; 
lean_inc_ref(v_body_3449_);
lean_inc_ref(v_binderType_3448_);
lean_dec_ref_known(v_a_3447_, 3);
v_u_3450_ = lean_ctor_get(v_binderType_3448_, 0);
lean_inc(v_u_3450_);
lean_dec_ref_known(v_binderType_3448_, 1);
v_u_3451_ = lean_ctor_get(v_body_3449_, 0);
lean_inc(v_u_3451_);
lean_dec_ref_known(v_body_3449_, 1);
lean_inc(v_a_3368_);
lean_inc_ref(v_a_3367_);
lean_inc(v_a_3366_);
lean_inc_ref(v_a_3365_);
lean_inc(v_fst_3410_);
v___x_3452_ = lean_infer_type(v_fst_3410_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
lean_inc(v_a_3368_);
lean_inc_ref(v_a_3367_);
lean_inc(v_a_3366_);
lean_inc_ref(v_a_3365_);
v___x_3454_ = lean_whnf(v_a_3453_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
if (lean_obj_tag(v_a_3455_) == 7)
{
lean_object* v_binderType_3456_; 
v_binderType_3456_ = lean_ctor_get(v_a_3455_, 1);
if (lean_obj_tag(v_binderType_3456_) == 3)
{
lean_object* v_body_3457_; 
v_body_3457_ = lean_ctor_get(v_a_3455_, 2);
if (lean_obj_tag(v_body_3457_) == 3)
{
lean_object* v_u_3458_; lean_object* v_u_3459_; lean_object* v___x_3460_; 
lean_inc_ref(v_body_3457_);
lean_inc_ref(v_binderType_3456_);
lean_dec_ref_known(v_a_3455_, 3);
v_u_3458_ = lean_ctor_get(v_binderType_3456_, 0);
lean_inc(v_u_3458_);
lean_dec_ref_known(v_binderType_3456_, 1);
v_u_3459_ = lean_ctor_get(v_body_3457_, 0);
lean_inc(v_u_3459_);
lean_dec_ref_known(v_body_3457_, 1);
v___x_3460_ = l_Lean_Meta_decLevel(v_u_3450_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v___x_3462_ = l_Lean_Meta_decLevel(v_u_3458_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3464_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref_known(v___x_3462_, 1);
lean_inc(v_a_3461_);
v___x_3464_ = l_Lean_Meta_isLevelDefEq(v_a_3461_, v_a_3463_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3629_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3629_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3629_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_unbox(v_a_3465_);
lean_dec(v_a_3465_);
if (v___x_3469_ == 1)
{
lean_object* v___x_3470_; 
lean_del_object(v___x_3467_);
v___x_3470_ = l_Lean_Meta_decLevel(v_u_3451_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3472_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref_known(v___x_3470_, 1);
v___x_3472_ = l_Lean_Meta_decLevel(v_u_3459_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v___x_3472_, 1);
v___x_3474_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3475_ = lean_box(0);
if (v_isShared_3428_ == 0)
{
lean_ctor_set_tag(v___x_3427_, 1);
lean_ctor_set(v___x_3427_, 1, v___x_3475_);
lean_ctor_set(v___x_3427_, 0, v_a_3473_);
v___x_3477_ = v___x_3427_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3473_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3479_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 1);
lean_ctor_set(v___x_3413_, 1, v___x_3477_);
lean_ctor_set(v___x_3413_, 0, v_a_3471_);
v___x_3479_ = v___x_3413_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3471_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3480_, 0, v_a_3461_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = l_Lean_Expr_const___override(v___x_3474_, v___x_3480_);
v___x_3482_ = lean_unsigned_to_nat(2u);
v___x_3483_ = lean_mk_empty_array_with_capacity(v___x_3482_);
lean_inc(v_fst_3424_);
v___x_3484_ = lean_array_push(v___x_3483_, v_fst_3424_);
lean_inc(v_fst_3410_);
v___x_3485_ = lean_array_push(v___x_3484_, v_fst_3410_);
v___x_3486_ = l_Lean_mkAppN(v___x_3481_, v___x_3485_);
lean_dec_ref(v___x_3485_);
v___x_3487_ = lean_box(0);
v___x_3488_ = l_Lean_Meta_trySynthInstance(v___x_3486_, v___x_3487_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3619_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3619_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3619_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
if (lean_obj_tag(v_a_3489_) == 1)
{
lean_object* v_a_3493_; lean_object* v___x_3494_; 
lean_del_object(v___x_3491_);
v_a_3493_ = lean_ctor_get(v_a_3489_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v_a_3489_, 1);
lean_inc(v_snd_3425_);
v___x_3494_ = l_Lean_Meta_getDecLevel(v_snd_3425_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3496_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
v___x_3496_ = l_Lean_Meta_getDecLevel(v_a_3397_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3498_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
lean_inc(v_a_3390_);
v___x_3498_ = l_Lean_Meta_getDecLevel(v_a_3390_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3500_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3501_, 0, v_a_3499_);
lean_ctor_set(v___x_3501_, 1, v___x_3475_);
v___x_3502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3502_, 0, v_a_3497_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3503_, 0, v_a_3495_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
lean_inc_ref(v___x_3503_);
v___x_3504_ = l_Lean_mkConst(v___x_3500_, v___x_3503_);
v___x_3505_ = lean_unsigned_to_nat(5u);
v___x_3506_ = lean_mk_empty_array_with_capacity(v___x_3505_);
lean_inc(v_fst_3424_);
v___x_3507_ = lean_array_push(v___x_3506_, v_fst_3424_);
lean_inc(v_fst_3410_);
v___x_3508_ = lean_array_push(v___x_3507_, v_fst_3410_);
lean_inc(v_a_3493_);
v___x_3509_ = lean_array_push(v___x_3508_, v_a_3493_);
lean_inc(v_snd_3425_);
v___x_3510_ = lean_array_push(v___x_3509_, v_snd_3425_);
lean_inc_ref(v_e_3363_);
v___x_3511_ = lean_array_push(v___x_3510_, v_e_3363_);
v___x_3512_ = l_Lean_mkAppN(v___x_3504_, v___x_3511_);
lean_dec_ref(v___x_3511_);
lean_inc(v_a_3368_);
lean_inc_ref(v_a_3367_);
lean_inc(v_a_3366_);
lean_inc_ref(v_a_3365_);
lean_inc_ref(v___x_3512_);
v___x_3513_ = lean_infer_type(v___x_3512_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
lean_inc(v_a_3390_);
v___x_3515_ = l_Lean_Meta_isExprDefEq(v_a_3390_, v_a_3514_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3610_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3610_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3610_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
uint8_t v___x_3520_; 
v___x_3520_ = lean_unbox(v_a_3516_);
lean_dec(v_a_3516_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; 
lean_del_object(v___x_3518_);
lean_dec_ref(v___x_3512_);
lean_del_object(v___x_3422_);
lean_inc(v_fst_3410_);
v___x_3521_ = l_Lean_Meta_isMonad_x3f(v_fst_3410_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3602_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3524_ = v___x_3521_;
v_isShared_3525_ = v_isSharedCheck_3602_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3521_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3602_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
if (lean_obj_tag(v_a_3522_) == 1)
{
lean_object* v_val_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3598_; 
lean_del_object(v___x_3524_);
v_val_3526_ = lean_ctor_get(v_a_3522_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_a_3522_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3528_ = v_a_3522_;
v_isShared_3529_ = v_isSharedCheck_3598_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_val_3526_);
lean_dec(v_a_3522_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3598_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; 
lean_inc(v_snd_3425_);
v___x_3530_ = l_Lean_Meta_getLevel(v_snd_3425_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3532_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
lean_inc(v_snd_3411_);
v___x_3532_ = l_Lean_Meta_getLevel(v_snd_3411_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___x_3532_, 1);
v___x_3534_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3535_ = 0;
v___x_3536_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3537_, 0, v_a_3533_);
lean_ctor_set(v___x_3537_, 1, v___x_3475_);
v___x_3538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3538_, 0, v_a_3531_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = l_Lean_mkConst(v___x_3536_, v___x_3538_);
v___x_3540_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3541_ = lean_unsigned_to_nat(3u);
v___x_3542_ = lean_mk_empty_array_with_capacity(v___x_3541_);
lean_inc_n(v_snd_3425_, 2);
v___x_3543_ = lean_array_push(v___x_3542_, v_snd_3425_);
v___x_3544_ = lean_array_push(v___x_3543_, v___x_3540_);
lean_inc(v_snd_3411_);
v___x_3545_ = lean_array_push(v___x_3544_, v_snd_3411_);
v___x_3546_ = l_Lean_mkAppN(v___x_3539_, v___x_3545_);
lean_dec_ref(v___x_3545_);
v___x_3547_ = l_Lean_mkForall(v___x_3534_, v___x_3535_, v_snd_3425_, v___x_3546_);
v___x_3548_ = l_Lean_Meta_trySynthInstance(v___x_3547_, v___x_3487_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3594_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3551_ = v___x_3548_;
v_isShared_3552_ = v_isSharedCheck_3594_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3548_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3594_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
if (lean_obj_tag(v_a_3549_) == 1)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
lean_del_object(v___x_3551_);
v_a_3553_ = lean_ctor_get(v_a_3549_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v_a_3549_, 1);
v___x_3554_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3555_ = l_Lean_mkConst(v___x_3554_, v___x_3503_);
v___x_3556_ = lean_unsigned_to_nat(8u);
v___x_3557_ = lean_mk_empty_array_with_capacity(v___x_3556_);
v___x_3558_ = lean_array_push(v___x_3557_, v_fst_3424_);
v___x_3559_ = lean_array_push(v___x_3558_, v_fst_3410_);
v___x_3560_ = lean_array_push(v___x_3559_, v_snd_3425_);
v___x_3561_ = lean_array_push(v___x_3560_, v_snd_3411_);
v___x_3562_ = lean_array_push(v___x_3561_, v_a_3493_);
v___x_3563_ = lean_array_push(v___x_3562_, v_a_3553_);
v___x_3564_ = lean_array_push(v___x_3563_, v_val_3526_);
v___x_3565_ = lean_array_push(v___x_3564_, v_e_3363_);
v___x_3566_ = l_Lean_mkAppN(v___x_3555_, v___x_3565_);
lean_dec_ref(v___x_3565_);
v___x_3567_ = l_Lean_Meta_expandCoe(v___x_3566_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v_fst_3569_; lean_object* v___x_3570_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v_fst_3569_ = lean_ctor_get(v_a_3568_, 0);
lean_inc_n(v_fst_3569_, 2);
lean_dec(v_a_3568_);
lean_inc(v_a_3368_);
lean_inc_ref(v_a_3367_);
lean_inc(v_a_3366_);
lean_inc_ref(v_a_3365_);
v___x_3570_ = lean_infer_type(v_fst_3569_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3570_, 1);
v___x_3572_ = l_Lean_Meta_isExprDefEq(v_a_3390_, v_a_3571_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3587_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3575_ = v___x_3572_;
v_isShared_3576_ = v_isSharedCheck_3587_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3587_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
uint8_t v___x_3577_; 
v___x_3577_ = lean_unbox(v_a_3573_);
lean_dec(v_a_3573_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3579_; 
lean_dec(v_fst_3569_);
lean_del_object(v___x_3528_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3487_);
v___x_3579_ = v___x_3575_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3487_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
else
{
lean_object* v___x_3582_; 
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v_fst_3569_);
v___x_3582_ = v___x_3528_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_fst_3569_);
v___x_3582_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3584_; 
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3582_);
v___x_3584_ = v___x_3575_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
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
}
else
{
lean_object* v_a_3588_; 
lean_dec(v_fst_3569_);
lean_del_object(v___x_3528_);
v_a_3588_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3588_);
lean_dec_ref_known(v___x_3572_, 1);
v_a_3371_ = v_a_3588_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3589_; 
lean_dec(v_fst_3569_);
lean_del_object(v___x_3528_);
lean_dec(v_a_3390_);
v_a_3589_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3570_, 1);
v_a_3371_ = v_a_3589_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3590_; 
lean_del_object(v___x_3528_);
lean_dec(v_a_3390_);
v_a_3590_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___x_3567_, 1);
v_a_3371_ = v_a_3590_;
goto v___jp_3370_;
}
}
else
{
lean_object* v___x_3592_; 
lean_dec(v_a_3549_);
lean_del_object(v___x_3528_);
lean_dec(v_val_3526_);
lean_dec_ref_known(v___x_3503_, 2);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3487_);
v___x_3592_ = v___x_3551_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3487_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v_a_3595_; 
lean_del_object(v___x_3528_);
lean_dec(v_val_3526_);
lean_dec_ref_known(v___x_3503_, 2);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3595_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3548_, 1);
v_a_3371_ = v_a_3595_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3596_; 
lean_dec(v_a_3531_);
lean_del_object(v___x_3528_);
lean_dec(v_val_3526_);
lean_dec_ref_known(v___x_3503_, 2);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3596_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3596_);
lean_dec_ref_known(v___x_3532_, 1);
v_a_3371_ = v_a_3596_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3597_; 
lean_del_object(v___x_3528_);
lean_dec(v_val_3526_);
lean_dec_ref_known(v___x_3503_, 2);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3597_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3530_, 1);
v_a_3371_ = v_a_3597_;
goto v___jp_3370_;
}
}
}
else
{
lean_object* v___x_3600_; 
lean_dec(v_a_3522_);
lean_dec_ref_known(v___x_3503_, 2);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3487_);
v___x_3600_ = v___x_3524_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3487_);
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
else
{
lean_object* v_a_3603_; 
lean_dec_ref_known(v___x_3503_, 2);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3603_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3521_, 1);
v_a_3371_ = v_a_3603_;
goto v___jp_3370_;
}
}
else
{
lean_object* v___x_3605_; 
lean_dec_ref_known(v___x_3503_, 2);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3512_);
v___x_3605_ = v___x_3422_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3512_);
v___x_3605_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3607_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3605_);
v___x_3607_ = v___x_3518_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
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
}
else
{
lean_object* v_a_3611_; 
lean_dec_ref(v___x_3512_);
lean_dec_ref_known(v___x_3503_, 2);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3611_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3515_, 1);
v_a_3371_ = v_a_3611_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3612_; 
lean_dec_ref(v___x_3512_);
lean_dec_ref_known(v___x_3503_, 2);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3612_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___x_3513_, 1);
v_a_3371_ = v_a_3612_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3613_; 
lean_dec(v_a_3497_);
lean_dec(v_a_3495_);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3613_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3498_, 1);
v_a_3371_ = v_a_3613_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3614_; 
lean_dec(v_a_3495_);
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3614_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3496_, 1);
v_a_3371_ = v_a_3614_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3615_; 
lean_dec(v_a_3493_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3615_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3494_, 1);
v_a_3371_ = v_a_3615_;
goto v___jp_3370_;
}
}
else
{
lean_object* v___x_3617_; 
lean_dec(v_a_3489_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3487_);
v___x_3617_ = v___x_3491_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3487_);
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
else
{
lean_object* v_a_3620_; 
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3620_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3620_);
lean_dec_ref_known(v___x_3488_, 1);
v_a_3371_ = v_a_3620_;
goto v___jp_3370_;
}
}
}
}
else
{
lean_object* v_a_3623_; 
lean_dec(v_a_3471_);
lean_dec(v_a_3461_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3623_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3472_, 1);
v_a_3371_ = v_a_3623_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3624_; 
lean_dec(v_a_3461_);
lean_dec(v_u_3459_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3624_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3470_, 1);
v_a_3371_ = v_a_3624_;
goto v___jp_3370_;
}
}
else
{
lean_object* v___x_3625_; lean_object* v___x_3627_; 
lean_dec(v_a_3461_);
lean_dec(v_u_3459_);
lean_dec(v_u_3451_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v___x_3625_ = lean_box(0);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3625_);
v___x_3627_ = v___x_3467_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
lean_object* v_a_3630_; 
lean_dec(v_a_3461_);
lean_dec(v_u_3459_);
lean_dec(v_u_3451_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3630_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3464_, 1);
v_a_3371_ = v_a_3630_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3631_; 
lean_dec(v_a_3461_);
lean_dec(v_u_3459_);
lean_dec(v_u_3451_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3631_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3462_, 1);
v_a_3371_ = v_a_3631_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3632_; 
lean_dec(v_u_3459_);
lean_dec(v_u_3458_);
lean_dec(v_u_3451_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3632_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___x_3460_, 1);
v_a_3371_ = v_a_3632_;
goto v___jp_3370_;
}
}
else
{
lean_object* v___x_3633_; 
lean_dec(v_u_3451_);
lean_dec(v_u_3450_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v___x_3633_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3455_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec_ref_known(v_a_3455_, 3);
v___y_3379_ = v___x_3633_;
goto v___jp_3378_;
}
}
else
{
lean_object* v___x_3634_; 
lean_dec(v_u_3451_);
lean_dec(v_u_3450_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v___x_3634_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3455_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec_ref_known(v_a_3455_, 3);
v___y_3379_ = v___x_3634_;
goto v___jp_3378_;
}
}
else
{
lean_object* v___x_3635_; 
lean_dec(v_u_3451_);
lean_dec(v_u_3450_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v___x_3635_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3455_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3455_);
v___y_3379_ = v___x_3635_;
goto v___jp_3378_;
}
}
else
{
lean_object* v_a_3636_; 
lean_dec(v_u_3451_);
lean_dec(v_u_3450_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3636_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3636_);
lean_dec_ref_known(v___x_3454_, 1);
v_a_3371_ = v_a_3636_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3637_; 
lean_dec(v_u_3451_);
lean_dec(v_u_3450_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3637_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3452_, 1);
v_a_3371_ = v_a_3637_;
goto v___jp_3370_;
}
}
else
{
lean_object* v___x_3638_; 
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v___x_3638_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3447_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec_ref_known(v_a_3447_, 3);
v___y_3379_ = v___x_3638_;
goto v___jp_3378_;
}
}
else
{
lean_object* v___x_3639_; 
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v___x_3639_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3447_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec_ref_known(v_a_3447_, 3);
v___y_3379_ = v___x_3639_;
goto v___jp_3378_;
}
}
else
{
lean_object* v___x_3640_; 
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v___x_3640_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3447_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3447_);
v___y_3379_ = v___x_3640_;
goto v___jp_3378_;
}
}
else
{
lean_object* v_a_3641_; 
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3641_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3641_);
lean_dec_ref_known(v___x_3446_, 1);
v_a_3371_ = v_a_3641_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3642_; 
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3642_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3444_, 1);
v_a_3371_ = v_a_3642_;
goto v___jp_3370_;
}
}
}
else
{
lean_object* v___x_3643_; 
lean_del_object(v___x_3434_);
lean_del_object(v___x_3427_);
lean_del_object(v___x_3413_);
lean_dec(v_a_3397_);
lean_dec(v_a_3390_);
v___x_3643_ = l_Lean_Meta_isMonad_x3f(v_fst_3410_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3736_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3736_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3736_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
if (lean_obj_tag(v_a_3644_) == 1)
{
lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3648_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v_fst_3424_);
v___x_3650_ = v___x_3422_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_fst_3424_);
v___x_3650_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3652_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v_snd_3425_);
v___x_3652_ = v___x_3408_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_snd_3425_);
v___x_3652_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3654_; 
if (v_isShared_3400_ == 0)
{
lean_ctor_set_tag(v___x_3399_, 1);
lean_ctor_set(v___x_3399_, 0, v_snd_3411_);
v___x_3654_ = v___x_3399_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_snd_3411_);
v___x_3654_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v_a_3657_; lean_object* v___x_3684_; 
v___x_3655_ = lean_box(0);
if (v_isShared_3393_ == 0)
{
lean_ctor_set_tag(v___x_3392_, 1);
lean_ctor_set(v___x_3392_, 0, v_e_3363_);
v___x_3684_ = v___x_3392_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_e_3363_);
v___x_3684_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3683_;
}
v___jp_3656_:
{
uint8_t v___x_3658_; 
v___x_3658_ = l_Lean_Exception_isInterrupt(v_a_3657_);
if (v___x_3658_ == 0)
{
uint8_t v___x_3659_; 
lean_inc_ref(v_a_3657_);
v___x_3659_ = l_Lean_Exception_isRuntime(v_a_3657_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; 
lean_dec_ref(v_a_3657_);
lean_del_object(v___x_3646_);
v___x_3660_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3430_, v_a_3366_, v_a_3368_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3667_ == 0)
{
lean_object* v_unused_3668_; 
v_unused_3668_ = lean_ctor_get(v___x_3660_, 0);
lean_dec(v_unused_3668_);
v___x_3662_ = v___x_3660_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_dec(v___x_3660_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3655_);
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3655_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
v_a_3669_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3660_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3660_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
else
{
lean_object* v___x_3678_; 
lean_dec(v_a_3430_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set_tag(v___x_3646_, 1);
lean_ctor_set(v___x_3646_, 0, v_a_3657_);
v___x_3678_ = v___x_3646_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3657_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
else
{
lean_object* v___x_3681_; 
lean_dec(v_a_3430_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set_tag(v___x_3646_, 1);
lean_ctor_set(v___x_3646_, 0, v_a_3657_);
v___x_3681_ = v___x_3646_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3657_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3685_ = lean_unsigned_to_nat(6u);
v___x_3686_ = lean_mk_empty_array_with_capacity(v___x_3685_);
v___x_3687_ = lean_array_push(v___x_3686_, v___x_3650_);
v___x_3688_ = lean_array_push(v___x_3687_, v___x_3652_);
v___x_3689_ = lean_array_push(v___x_3688_, v___x_3654_);
v___x_3690_ = lean_array_push(v___x_3689_, v___x_3655_);
v___x_3691_ = lean_array_push(v___x_3690_, v_a_3644_);
v___x_3692_ = lean_array_push(v___x_3691_, v___x_3684_);
v___x_3693_ = l_Lean_Meta_mkAppOptM(v___x_3648_, v___x_3692_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3712_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3696_ = v___x_3693_;
v_isShared_3697_ = v_isSharedCheck_3712_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3693_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3712_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_Meta_expandCoe(v_a_3694_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3710_; 
lean_del_object(v___x_3646_);
lean_dec(v_a_3430_);
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3710_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3710_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v_fst_3703_; lean_object* v___x_3705_; 
v_fst_3703_ = lean_ctor_get(v_a_3699_, 0);
lean_inc(v_fst_3703_);
lean_dec(v_a_3699_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set_tag(v___x_3696_, 1);
lean_ctor_set(v___x_3696_, 0, v_fst_3703_);
v___x_3705_ = v___x_3696_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_fst_3703_);
v___x_3705_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3707_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3705_);
v___x_3707_ = v___x_3701_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
else
{
lean_object* v_a_3711_; 
lean_del_object(v___x_3696_);
v_a_3711_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3698_, 1);
v_a_3657_ = v_a_3711_;
goto v___jp_3656_;
}
}
}
else
{
lean_object* v_a_3713_; 
v_a_3713_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3693_, 1);
v_a_3657_ = v_a_3713_;
goto v___jp_3656_;
}
}
}
}
}
}
else
{
lean_object* v___x_3718_; 
lean_del_object(v___x_3646_);
lean_dec(v_a_3644_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3411_);
lean_del_object(v___x_3408_);
lean_del_object(v___x_3399_);
lean_del_object(v___x_3392_);
lean_dec_ref(v_e_3363_);
v___x_3718_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3430_, v_a_3366_, v_a_3368_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3726_; 
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; 
v_unused_3727_ = lean_ctor_get(v___x_3718_, 0);
lean_dec(v_unused_3727_);
v___x_3720_ = v___x_3718_;
v_isShared_3721_ = v_isSharedCheck_3726_;
goto v_resetjp_3719_;
}
else
{
lean_dec(v___x_3718_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3726_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3722_ = lean_box(0);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3722_);
v___x_3724_ = v___x_3720_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
v_a_3728_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3718_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3718_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3430_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_dec(v_snd_3411_);
lean_del_object(v___x_3408_);
lean_del_object(v___x_3399_);
lean_del_object(v___x_3392_);
lean_dec_ref(v_e_3363_);
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_a_3430_);
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_del_object(v___x_3408_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3738_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3431_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3431_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_del_object(v___x_3427_);
lean_dec(v_snd_3425_);
lean_dec(v_fst_3424_);
lean_del_object(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_del_object(v___x_3408_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3746_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3429_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3429_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
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
}
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_dec(v_a_3416_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_del_object(v___x_3408_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v___x_3756_ = lean_box(0);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3756_);
v___x_3758_ = v___x_3418_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
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
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v_fst_3410_);
lean_del_object(v___x_3408_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3761_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3415_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3415_);
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
lean_object* v___x_3771_; lean_object* v___x_3773_; 
lean_dec(v_a_3402_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v___x_3771_ = lean_box(0);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3771_);
v___x_3773_ = v___x_3404_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
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
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3776_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3401_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3401_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_dec_ref(v_e_3363_);
v_a_3785_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3394_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3394_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3794_, lean_object* v_expectedType_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3794_, v_expectedType_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3802_, lean_object* v_expectedType_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v___x_3809_; 
lean_inc_ref(v_expectedType_3803_);
lean_inc_ref(v_expr_3802_);
v___x_3809_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3802_, v_expectedType_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3889_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3812_ = v___x_3809_;
v_isShared_3813_ = v_isSharedCheck_3889_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3809_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3889_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
if (lean_obj_tag(v_a_3810_) == 1)
{
lean_object* v_val_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3826_; 
lean_dec_ref(v_expectedType_3803_);
lean_dec_ref(v_expr_3802_);
v_val_3814_ = lean_ctor_get(v_a_3810_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_a_3810_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3816_ = v_a_3810_;
v_isShared_3817_ = v_isSharedCheck_3826_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_val_3814_);
lean_dec(v_a_3810_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3826_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
v___x_3818_ = lean_box(0);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v_val_3814_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v___x_3819_);
v___x_3821_ = v___x_3816_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3819_);
v___x_3821_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3823_; 
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v___x_3821_);
v___x_3823_ = v___x_3812_;
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
lean_object* v___x_3827_; 
lean_del_object(v___x_3812_);
lean_dec(v_a_3810_);
lean_inc_ref(v_expectedType_3803_);
v___x_3827_ = l_Lean_Meta_whnfR(v_expectedType_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; uint8_t v___x_3829_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___x_3827_, 1);
v___x_3829_ = l_Lean_Expr_isForall(v_a_3828_);
lean_dec(v_a_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3802_, v_expectedType_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
return v___x_3830_;
}
else
{
lean_object* v___x_3831_; 
lean_inc_ref(v_expr_3802_);
v___x_3831_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3802_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___x_3831_, 1);
if (lean_obj_tag(v_a_3832_) == 1)
{
lean_object* v_val_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3871_; 
v_val_3833_ = lean_ctor_get(v_a_3832_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v_a_3832_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3835_ = v_a_3832_;
v_isShared_3836_ = v_isSharedCheck_3871_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_val_3833_);
lean_dec(v_a_3832_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3871_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; 
lean_inc(v_a_3807_);
lean_inc_ref(v_a_3806_);
lean_inc(v_a_3805_);
lean_inc_ref(v_a_3804_);
lean_inc(v_val_3833_);
v___x_3837_ = lean_infer_type(v_val_3833_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3839_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3837_, 1);
lean_inc_ref(v_expectedType_3803_);
v___x_3839_ = l_Lean_Meta_isExprDefEq(v_a_3838_, v_expectedType_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3854_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3842_ = v___x_3839_;
v_isShared_3843_ = v_isSharedCheck_3854_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3854_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
uint8_t v___x_3844_; 
v___x_3844_ = lean_unbox(v_a_3840_);
lean_dec(v_a_3840_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; 
lean_del_object(v___x_3842_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
v___x_3845_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3802_, v_expectedType_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
return v___x_3845_;
}
else
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3849_; 
lean_dec_ref(v_expectedType_3803_);
lean_dec_ref(v_expr_3802_);
v___x_3846_ = lean_box(0);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v_val_3833_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v___x_3847_);
v___x_3849_ = v___x_3835_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3851_; 
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3849_);
v___x_3851_ = v___x_3842_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_dec_ref(v_expectedType_3803_);
lean_dec_ref(v_expr_3802_);
v_a_3855_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3839_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3839_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
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
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_dec_ref(v_expectedType_3803_);
lean_dec_ref(v_expr_3802_);
v_a_3863_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3837_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3837_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
}
else
{
lean_object* v___x_3872_; 
lean_dec(v_a_3832_);
v___x_3872_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3802_, v_expectedType_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
return v___x_3872_;
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec_ref(v_expectedType_3803_);
lean_dec_ref(v_expr_3802_);
v_a_3873_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3831_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3831_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec_ref(v_expectedType_3803_);
lean_dec_ref(v_expr_3802_);
v_a_3881_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3827_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3827_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec_ref(v_expectedType_3803_);
lean_dec_ref(v_expr_3802_);
v_a_3890_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3809_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3809_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3898_, lean_object* v_expectedType_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3898_, v_expectedType_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3906_, lean_object* v_expectedType_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3906_, v_expectedType_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3938_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3938_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3938_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
switch(lean_obj_tag(v_a_3914_))
{
case 0:
{
lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3918_ = lean_box(0);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3918_);
v___x_3920_ = v___x_3916_;
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
case 1:
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3933_; 
v_a_3922_ = lean_ctor_get(v_a_3914_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_a_3914_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3924_ = v_a_3914_;
v_isShared_3925_ = v_isSharedCheck_3933_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v_a_3914_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3933_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v_fst_3926_; lean_object* v___x_3928_; 
v_fst_3926_ = lean_ctor_get(v_a_3922_, 0);
lean_inc(v_fst_3926_);
lean_dec(v_a_3922_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 0, v_fst_3926_);
v___x_3928_ = v___x_3924_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_fst_3926_);
v___x_3928_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3930_; 
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3928_);
v___x_3930_ = v___x_3916_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3928_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
default: 
{
lean_object* v___x_3934_; lean_object* v___x_3936_; 
v___x_3934_ = lean_box(2);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3934_);
v___x_3936_ = v___x_3916_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
v_a_3939_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3913_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3913_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3947_, lean_object* v_expectedType_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lean_Meta_coerce_x3f(v_expr_3947_, v_expectedType_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
lean_dec(v_a_3950_);
lean_dec_ref(v_a_3949_);
return v_res_3954_;
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
