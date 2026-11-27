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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArgD(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMonad_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
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
size_t v_x_38550__boxed_231_; uint8_t v_res_232_; lean_object* v_r_233_; 
v_x_38550__boxed_231_ = lean_unbox_usize(v_x_229_);
lean_dec(v_x_229_);
v_res_232_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_228_, v_x_38550__boxed_231_, v_x_230_);
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
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0);
v___x_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
lean_ctor_set(v___x_348_, 2, v___x_346_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_349_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_350_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
v___x_351_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0);
v___x_352_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
v___x_353_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
lean_ctor_set(v___x_353_, 2, v___x_350_);
lean_ctor_set(v___x_353_, 3, v___x_351_);
lean_ctor_set(v___x_353_, 4, v___x_351_);
lean_ctor_set(v___x_353_, 5, v___x_351_);
lean_ctor_set(v___x_353_, 6, v___x_349_);
return v___x_353_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_PersistentHashMap_empty___redArg();
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v_cls_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_cls_369_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_370_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15));
v___x_371_ = l_Lean_Name_append(v___x_370_, v_cls_369_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_382_, uint8_t v_isMeta_383_, lean_object* v_hint_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_env_427_; uint8_t v_isExporting_428_; lean_object* v_entry_429_; lean_object* v___x_430_; lean_object* v_env_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_425_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6);
v___x_426_ = lean_st_ref_get(v___y_389_);
v_env_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc_ref(v_env_427_);
lean_dec(v___x_426_);
v_isExporting_428_ = lean_ctor_get_uint8(v_env_427_, sizeof(void*)*13);
lean_dec_ref(v_env_427_);
lean_inc(v_mod_382_);
v_entry_429_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_429_, 0, v_mod_382_);
lean_ctor_set_uint8(v_entry_429_, sizeof(void*)*1, v_isExporting_428_);
lean_ctor_set_uint8(v_entry_429_, sizeof(void*)*1 + 1, v_isMeta_383_);
v___x_430_ = lean_st_ref_get(v___y_389_);
v_env_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc_ref(v_env_431_);
lean_dec(v___x_430_);
v___x_432_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_433_ = lean_box(1);
v___x_434_ = lean_box(0);
v___x_435_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_425_, v___x_432_, v_env_431_, v___x_433_, v___x_434_);
v___x_436_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_435_, v_entry_429_);
lean_dec(v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v_toCold_437_; lean_object* v_options_438_; lean_object* v_inheritedTraceOptions_439_; uint8_t v_hasTrace_440_; lean_object* v___f_441_; uint8_t v___x_442_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; 
v_toCold_437_ = lean_ctor_get(v___y_388_, 0);
v_options_438_ = lean_ctor_get(v_toCold_437_, 2);
v_inheritedTraceOptions_439_ = lean_ctor_get(v_toCold_437_, 11);
v_hasTrace_440_ = lean_ctor_get_uint8(v_options_438_, sizeof(void*)*1);
v___f_441_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_441_, 0, v___x_432_);
lean_closure_set(v___f_441_, 1, v_entry_429_);
v___x_442_ = 1;
if (v_hasTrace_440_ == 0)
{
lean_dec(v_hint_384_);
lean_dec(v_mod_382_);
v___y_444_ = v___y_385_;
v___y_445_ = v___y_387_;
v___y_446_ = v___y_389_;
goto v___jp_443_;
}
else
{
lean_object* v_cls_473_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_cls_473_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_495_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
v___x_496_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_439_, v_options_438_, v___x_495_);
if (v___x_496_ == 0)
{
lean_dec(v_hint_384_);
lean_dec(v_mod_382_);
v___y_444_ = v___y_385_;
v___y_445_ = v___y_387_;
v___y_446_ = v___y_389_;
goto v___jp_443_;
}
else
{
lean_object* v___x_497_; lean_object* v___y_499_; 
v___x_497_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
if (v_isExporting_428_ == 0)
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23));
v___y_499_ = v___x_506_;
goto v___jp_498_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24));
v___y_499_ = v___x_507_;
goto v___jp_498_;
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_inc_ref(v___y_499_);
v___x_500_ = l_Lean_stringToMessageData(v___y_499_);
v___x_501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_497_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20);
v___x_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
if (v_isMeta_383_ == 0)
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_482_ = v___x_503_;
v___y_483_ = v___x_504_;
goto v___jp_481_;
}
else
{
lean_object* v___x_505_; 
v___x_505_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
v___y_482_ = v___x_503_;
v___y_483_ = v___x_505_;
goto v___jp_481_;
}
}
}
v___jp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___y_475_);
lean_ctor_set(v___x_477_, 1, v___y_476_);
v___x_478_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3(v_cls_473_, v___x_477_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v_snd_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v_snd_480_ = lean_ctor_get(v_a_479_, 1);
lean_inc(v_snd_480_);
lean_dec(v_a_479_);
v___y_444_ = v_snd_480_;
v___y_445_ = v___y_387_;
v___y_446_ = v___y_389_;
goto v___jp_443_;
}
else
{
lean_dec_ref(v___f_441_);
return v___x_478_;
}
}
v___jp_481_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
lean_inc_ref(v___y_483_);
v___x_484_ = l_Lean_stringToMessageData(v___y_483_);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___y_482_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_MessageData_ofName(v_mod_382_);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_Name_isAnonymous(v_hint_384_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12);
v___x_492_ = l_Lean_MessageData_ofName(v_hint_384_);
v___x_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___y_475_ = v___x_489_;
v___y_476_ = v___x_493_;
goto v___jp_474_;
}
else
{
lean_object* v___x_494_; 
lean_dec(v_hint_384_);
v___x_494_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13);
v___y_475_ = v___x_489_;
v___y_476_ = v___x_494_;
goto v___jp_474_;
}
}
}
v___jp_443_:
{
lean_object* v___x_447_; lean_object* v_toEnvExtension_448_; uint8_t v_logWrites_449_; 
v___x_447_ = lean_st_ref_take(v___y_446_);
v_toEnvExtension_448_ = lean_ctor_get(v___x_432_, 0);
v_logWrites_449_ = lean_ctor_get_uint8(v_toEnvExtension_448_, sizeof(void*)*6);
if (v_logWrites_449_ == 0)
{
lean_object* v_env_450_; lean_object* v_nextMacroScope_451_; lean_object* v_ngen_452_; lean_object* v_auxDeclNGen_453_; lean_object* v_traceState_454_; lean_object* v_recordedDeps_455_; lean_object* v_messages_456_; lean_object* v_infoState_457_; lean_object* v_snapshotTasks_458_; lean_object* v_asyncMode_459_; lean_object* v___x_460_; 
v_env_450_ = lean_ctor_get(v___x_447_, 0);
lean_inc_ref(v_env_450_);
v_nextMacroScope_451_ = lean_ctor_get(v___x_447_, 1);
lean_inc(v_nextMacroScope_451_);
v_ngen_452_ = lean_ctor_get(v___x_447_, 2);
lean_inc_ref(v_ngen_452_);
v_auxDeclNGen_453_ = lean_ctor_get(v___x_447_, 3);
lean_inc_ref(v_auxDeclNGen_453_);
v_traceState_454_ = lean_ctor_get(v___x_447_, 4);
lean_inc_ref(v_traceState_454_);
v_recordedDeps_455_ = lean_ctor_get(v___x_447_, 6);
lean_inc_ref(v_recordedDeps_455_);
v_messages_456_ = lean_ctor_get(v___x_447_, 7);
lean_inc_ref(v_messages_456_);
v_infoState_457_ = lean_ctor_get(v___x_447_, 8);
lean_inc_ref(v_infoState_457_);
v_snapshotTasks_458_ = lean_ctor_get(v___x_447_, 9);
lean_inc_ref(v_snapshotTasks_458_);
lean_dec(v___x_447_);
v_asyncMode_459_ = lean_ctor_get(v_toEnvExtension_448_, 2);
lean_inc_ref(v_toEnvExtension_448_);
v___x_460_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_448_, v_env_450_, v___f_441_, v_asyncMode_459_, v___x_434_, v___x_442_);
v___y_392_ = v_traceState_454_;
v___y_393_ = v_ngen_452_;
v___y_394_ = v_nextMacroScope_451_;
v___y_395_ = v_recordedDeps_455_;
v___y_396_ = v_snapshotTasks_458_;
v___y_397_ = v_infoState_457_;
v___y_398_ = v___y_446_;
v___y_399_ = v_messages_456_;
v___y_400_ = v___y_444_;
v___y_401_ = v_auxDeclNGen_453_;
v___y_402_ = v___y_445_;
v___y_403_ = v___x_460_;
goto v___jp_391_;
}
else
{
lean_object* v_env_461_; lean_object* v_nextMacroScope_462_; lean_object* v_ngen_463_; lean_object* v_auxDeclNGen_464_; lean_object* v_traceState_465_; lean_object* v_recordedDeps_466_; lean_object* v_messages_467_; lean_object* v_infoState_468_; lean_object* v_snapshotTasks_469_; lean_object* v_asyncMode_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_env_461_ = lean_ctor_get(v___x_447_, 0);
lean_inc_ref(v_env_461_);
v_nextMacroScope_462_ = lean_ctor_get(v___x_447_, 1);
lean_inc(v_nextMacroScope_462_);
v_ngen_463_ = lean_ctor_get(v___x_447_, 2);
lean_inc_ref(v_ngen_463_);
v_auxDeclNGen_464_ = lean_ctor_get(v___x_447_, 3);
lean_inc_ref(v_auxDeclNGen_464_);
v_traceState_465_ = lean_ctor_get(v___x_447_, 4);
lean_inc_ref(v_traceState_465_);
v_recordedDeps_466_ = lean_ctor_get(v___x_447_, 6);
lean_inc_ref(v_recordedDeps_466_);
v_messages_467_ = lean_ctor_get(v___x_447_, 7);
lean_inc_ref(v_messages_467_);
v_infoState_468_ = lean_ctor_get(v___x_447_, 8);
lean_inc_ref(v_infoState_468_);
v_snapshotTasks_469_ = lean_ctor_get(v___x_447_, 9);
lean_inc_ref(v_snapshotTasks_469_);
lean_dec(v___x_447_);
v_asyncMode_470_ = lean_ctor_get(v_toEnvExtension_448_, 2);
lean_inc_ref_n(v_toEnvExtension_448_, 2);
v___x_471_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_448_, v_env_461_);
lean_dec_ref(v_env_461_);
v___x_472_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_448_, v___x_471_, v___f_441_, v_asyncMode_470_, v___x_434_, v___x_442_);
v___y_392_ = v_traceState_465_;
v___y_393_ = v_ngen_463_;
v___y_394_ = v_nextMacroScope_462_;
v___y_395_ = v_recordedDeps_466_;
v___y_396_ = v_snapshotTasks_469_;
v___y_397_ = v_infoState_468_;
v___y_398_ = v___y_446_;
v___y_399_ = v_messages_467_;
v___y_400_ = v___y_444_;
v___y_401_ = v_auxDeclNGen_464_;
v___y_402_ = v___y_445_;
v___y_403_ = v___x_472_;
goto v___jp_391_;
}
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec_ref_known(v_entry_429_, 1);
lean_dec(v_hint_384_);
lean_dec(v_mod_382_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___y_385_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
v___jp_391_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_mctx_408_; lean_object* v_zetaDeltaFVarIds_409_; lean_object* v_postponed_410_; lean_object* v_diag_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_423_; 
v___x_404_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1);
v___x_405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_405_, 0, v___y_403_);
lean_ctor_set(v___x_405_, 1, v___y_394_);
lean_ctor_set(v___x_405_, 2, v___y_393_);
lean_ctor_set(v___x_405_, 3, v___y_401_);
lean_ctor_set(v___x_405_, 4, v___y_392_);
lean_ctor_set(v___x_405_, 5, v___x_404_);
lean_ctor_set(v___x_405_, 6, v___y_395_);
lean_ctor_set(v___x_405_, 7, v___y_399_);
lean_ctor_set(v___x_405_, 8, v___y_397_);
lean_ctor_set(v___x_405_, 9, v___y_396_);
v___x_406_ = lean_st_ref_put(v___y_398_, v___x_405_);
v___x_407_ = lean_st_ref_take(v___y_402_);
v_mctx_408_ = lean_ctor_get(v___x_407_, 0);
v_zetaDeltaFVarIds_409_ = lean_ctor_get(v___x_407_, 2);
v_postponed_410_ = lean_ctor_get(v___x_407_, 3);
v_diag_411_ = lean_ctor_get(v___x_407_, 4);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_407_, 1);
lean_dec(v_unused_424_);
v___x_413_ = v___x_407_;
v_isShared_414_ = v_isSharedCheck_423_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_diag_411_);
lean_inc(v_postponed_410_);
lean_inc(v_zetaDeltaFVarIds_409_);
lean_inc(v_mctx_408_);
lean_dec(v___x_407_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_423_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_415_ = lean_box(0);
v___x_416_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_416_);
v___x_418_ = v___x_413_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_mctx_408_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_zetaDeltaFVarIds_409_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_postponed_410_);
lean_ctor_set(v_reuseFailAlloc_422_, 4, v_diag_411_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_st_ref_put(v___y_402_, v___x_418_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_415_);
lean_ctor_set(v___x_420_, 1, v___y_400_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object* v_mod_511_, lean_object* v_isMeta_512_, lean_object* v_hint_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
uint8_t v_isMeta_boxed_520_; lean_object* v_res_521_; 
v_isMeta_boxed_520_ = lean_unbox(v_isMeta_512_);
v_res_521_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_511_, v_isMeta_boxed_520_, v_hint_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
lean_object* v___x_524_; 
v___x_524_ = lean_box(0);
return v___x_524_;
}
else
{
lean_object* v_key_525_; lean_object* v_value_526_; lean_object* v_tail_527_; uint8_t v___x_528_; 
v_key_525_ = lean_ctor_get(v_x_523_, 0);
v_value_526_ = lean_ctor_get(v_x_523_, 1);
v_tail_527_ = lean_ctor_get(v_x_523_, 2);
v___x_528_ = lean_name_eq(v_key_525_, v_a_522_);
if (v___x_528_ == 0)
{
v_x_523_ = v_tail_527_;
goto _start;
}
else
{
lean_object* v___x_530_; 
lean_inc(v_value_526_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_value_526_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_531_, lean_object* v_x_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(v_a_531_, v_x_532_);
lean_dec(v_x_532_);
lean_dec(v_a_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_buckets_536_; lean_object* v___x_537_; uint64_t v___y_539_; 
v_buckets_536_ = lean_ctor_get(v_m_534_, 1);
v___x_537_ = lean_array_get_size(v_buckets_536_);
if (lean_obj_tag(v_a_535_) == 0)
{
uint64_t v___x_553_; 
v___x_553_ = 1723ULL;
v___y_539_ = v___x_553_;
goto v___jp_538_;
}
else
{
uint64_t v_hash_554_; 
v_hash_554_ = lean_ctor_get_uint64(v_a_535_, sizeof(void*)*2);
v___y_539_ = v_hash_554_;
goto v___jp_538_;
}
v___jp_538_:
{
uint64_t v___x_540_; uint64_t v___x_541_; uint64_t v_fold_542_; uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v___x_545_; size_t v___x_546_; size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_540_ = 32ULL;
v___x_541_ = lean_uint64_shift_right(v___y_539_, v___x_540_);
v_fold_542_ = lean_uint64_xor(v___y_539_, v___x_541_);
v___x_543_ = 16ULL;
v___x_544_ = lean_uint64_shift_right(v_fold_542_, v___x_543_);
v___x_545_ = lean_uint64_xor(v_fold_542_, v___x_544_);
v___x_546_ = lean_uint64_to_usize(v___x_545_);
v___x_547_ = lean_usize_of_nat(v___x_537_);
v___x_548_ = ((size_t)1ULL);
v___x_549_ = lean_usize_sub(v___x_547_, v___x_548_);
v___x_550_ = lean_usize_land(v___x_546_, v___x_549_);
v___x_551_ = lean_array_uget_borrowed(v_buckets_536_, v___x_550_);
v___x_552_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(v_a_535_, v___x_551_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_555_, v_a_556_);
lean_dec(v_a_556_);
lean_dec_ref(v_m_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_558_, lean_object* v_declName_559_, lean_object* v_as_560_, size_t v_sz_561_, size_t v_i_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_lt(v_i_562_, v_sz_561_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v_declName_559_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_b_563_);
lean_ctor_set(v___x_571_, 1, v___y_564_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v_modules_574_; lean_object* v___x_575_; lean_object* v_a_576_; lean_object* v___x_577_; lean_object* v_toImport_578_; lean_object* v_module_579_; lean_object* v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; 
v___x_573_ = l_Lean_Environment_header(v___x_558_);
v_modules_574_ = lean_ctor_get(v___x_573_, 3);
lean_inc_ref(v_modules_574_);
lean_dec_ref(v___x_573_);
v___x_575_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_576_ = lean_array_uget_borrowed(v_as_560_, v_i_562_);
v___x_577_ = lean_array_get(v___x_575_, v_modules_574_, v_a_576_);
lean_dec_ref(v_modules_574_);
v_toImport_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc_ref(v_toImport_578_);
lean_dec(v___x_577_);
v_module_579_ = lean_ctor_get(v_toImport_578_, 0);
lean_inc(v_module_579_);
lean_dec_ref(v_toImport_578_);
v___x_580_ = lean_box(0);
v___x_581_ = 0;
lean_inc(v_declName_559_);
v___x_582_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_579_, v___x_581_, v_declName_559_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v_snd_584_; size_t v___x_585_; size_t v___x_586_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v_snd_584_ = lean_ctor_get(v_a_583_, 1);
lean_inc(v_snd_584_);
lean_dec(v_a_583_);
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_add(v_i_562_, v___x_585_);
v_i_562_ = v___x_586_;
v_b_563_ = v___x_580_;
v___y_564_ = v_snd_584_;
goto _start;
}
else
{
lean_dec(v_declName_559_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_588_, lean_object* v_declName_589_, lean_object* v_as_590_, lean_object* v_sz_591_, lean_object* v_i_592_, lean_object* v_b_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
size_t v_sz_boxed_600_; size_t v_i_boxed_601_; lean_object* v_res_602_; 
v_sz_boxed_600_ = lean_unbox_usize(v_sz_591_);
lean_dec(v_sz_591_);
v_i_boxed_601_ = lean_unbox_usize(v_i_592_);
lean_dec(v_i_592_);
v_res_602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_588_, v_declName_589_, v_as_590_, v_sz_boxed_600_, v_i_boxed_601_, v_b_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec_ref(v_as_590_);
lean_dec_ref(v___x_588_);
return v_res_602_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_HashMap_instInhabited___redArg();
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_606_, uint8_t v_isMeta_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_env_620_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___x_645_; 
v___x_614_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0);
v___x_615_ = lean_st_ref_get(v___y_612_);
v_env_620_ = lean_ctor_get(v___x_615_, 0);
lean_inc_ref(v_env_620_);
lean_dec(v___x_615_);
v___x_645_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_620_, v_declName_606_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_dec_ref(v_env_620_);
lean_dec(v_declName_606_);
goto v___jp_616_;
}
else
{
lean_object* v_val_646_; lean_object* v___x_647_; lean_object* v_modules_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = l_Lean_Environment_header(v_env_620_);
v_modules_648_ = lean_ctor_get(v___x_647_, 3);
lean_inc_ref(v_modules_648_);
lean_dec_ref(v___x_647_);
v___x_649_ = lean_array_get_size(v_modules_648_);
v___x_650_ = lean_nat_dec_lt(v_val_646_, v___x_649_);
if (v___x_650_ == 0)
{
lean_dec_ref(v_modules_648_);
lean_dec(v_val_646_);
lean_dec_ref(v_env_620_);
lean_dec(v_declName_606_);
goto v___jp_616_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___y_654_; 
v___x_651_ = lean_array_fget(v_modules_648_, v_val_646_);
lean_dec(v_val_646_);
lean_dec_ref(v_modules_648_);
v___x_652_ = lean_st_ref_get(v___y_612_);
if (v_isMeta_607_ == 0)
{
lean_dec(v___x_652_);
v___y_654_ = v_isMeta_607_;
goto v___jp_653_;
}
else
{
lean_object* v_env_667_; uint8_t v___x_668_; 
v_env_667_ = lean_ctor_get(v___x_652_, 0);
lean_inc_ref(v_env_667_);
lean_dec(v___x_652_);
lean_inc(v_declName_606_);
v___x_668_ = l_Lean_isMarkedMeta(v_env_667_, v_declName_606_);
if (v___x_668_ == 0)
{
v___y_654_ = v_isMeta_607_;
goto v___jp_653_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = 0;
v___y_654_ = v___x_669_;
goto v___jp_653_;
}
}
v___jp_653_:
{
lean_object* v_toImport_655_; lean_object* v_module_656_; lean_object* v___x_657_; 
v_toImport_655_ = lean_ctor_get(v___x_651_, 0);
lean_inc_ref(v_toImport_655_);
lean_dec(v___x_651_);
v_module_656_ = lean_ctor_get(v_toImport_655_, 0);
lean_inc(v_module_656_);
lean_dec_ref(v_toImport_655_);
lean_inc(v_declName_606_);
v___x_657_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_656_, v___y_654_, v_declName_606_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v_snd_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v_snd_659_ = lean_ctor_get(v_a_658_, 1);
lean_inc(v_snd_659_);
lean_dec(v_a_658_);
v___x_660_ = l_Lean_indirectModUseExt;
v___x_661_ = lean_box(1);
v___x_662_ = lean_box(0);
lean_inc_ref(v_env_620_);
v___x_663_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_614_, v___x_660_, v_env_620_, v___x_661_, v___x_662_);
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_663_, v_declName_606_);
lean_dec(v___x_663_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v___x_665_; 
v___x_665_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___y_622_ = v_snd_659_;
v___y_623_ = v___x_665_;
goto v___jp_621_;
}
else
{
lean_object* v_val_666_; 
v_val_666_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v___x_664_, 1);
v___y_622_ = v_snd_659_;
v___y_623_ = v_val_666_;
goto v___jp_621_;
}
}
else
{
lean_dec_ref(v_env_620_);
lean_dec(v_declName_606_);
return v___x_657_;
}
}
}
}
v___jp_616_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_box(0);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___y_608_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
v___jp_621_:
{
lean_object* v___x_624_; size_t v_sz_625_; size_t v___x_626_; lean_object* v___x_627_; 
v___x_624_ = lean_box(0);
v_sz_625_ = lean_array_size(v___y_623_);
v___x_626_ = ((size_t)0ULL);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_620_, v_declName_606_, v___y_623_, v_sz_625_, v___x_626_, v___x_624_, v___y_622_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec_ref(v___y_623_);
lean_dec_ref(v_env_620_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_644_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_644_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_644_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_644_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_snd_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_642_; 
v_snd_632_ = lean_ctor_get(v_a_628_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_a_628_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v_a_628_, 0);
lean_dec(v_unused_643_);
v___x_634_ = v_a_628_;
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_snd_632_);
lean_dec(v_a_628_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_624_);
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_snd_632_);
v___x_637_ = v_reuseFailAlloc_641_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_637_);
v___x_639_ = v___x_630_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
else
{
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_670_, lean_object* v_isMeta_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
uint8_t v_isMeta_boxed_678_; lean_object* v_res_679_; 
v_isMeta_boxed_678_ = lean_unbox(v_isMeta_671_);
v_res_679_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_670_, v_isMeta_boxed_678_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___y_695_; lean_object* v_f_699_; uint8_t v___x_700_; 
v_f_699_ = l_Lean_Expr_getAppFn(v_e_687_);
v___x_700_ = l_Lean_Expr_isConst(v_f_699_);
if (v___x_700_ == 0)
{
lean_dec_ref(v_f_699_);
lean_dec_ref(v_e_687_);
v___y_695_ = v___y_688_;
goto v___jp_694_;
}
else
{
lean_object* v_declName_701_; lean_object* v___x_702_; lean_object* v_env_703_; uint8_t v___x_704_; 
v_declName_701_ = l_Lean_Expr_constName_x21(v_f_699_);
lean_dec_ref(v_f_699_);
v___x_702_ = lean_st_ref_get(v___y_692_);
v_env_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc_ref(v_env_703_);
lean_dec(v___x_702_);
lean_inc(v_declName_701_);
v___x_704_ = l_Lean_Meta_isCoeDecl(v_env_703_, v_declName_701_);
if (v___x_704_ == 0)
{
lean_dec(v_declName_701_);
lean_dec_ref(v_e_687_);
v___y_695_ = v___y_688_;
goto v___jp_694_;
}
else
{
lean_object* v___x_705_; 
lean_inc(v_declName_701_);
lean_inc_ref(v_e_687_);
v___x_705_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_687_, v_declName_701_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; uint8_t v___x_707_; lean_object* v___x_708_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = 0;
v___x_708_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_706_, v___x_707_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_761_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v_snd_710_ = lean_ctor_get(v_a_709_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_a_709_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v_a_709_, 0);
lean_dec(v_unused_762_);
v___x_712_ = v_a_709_;
v_isShared_713_ = v_isSharedCheck_761_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_dec(v_a_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_761_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; 
lean_inc_ref(v_e_687_);
v___x_714_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_687_, v___x_707_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_752_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_752_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_752_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_752_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
if (lean_obj_tag(v_a_715_) == 1)
{
lean_object* v_val_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_751_; 
v_val_719_ = lean_ctor_get(v_a_715_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_a_715_);
if (v_isSharedCheck_751_ == 0)
{
v___x_721_ = v_a_715_;
v_isShared_722_ = v_isSharedCheck_751_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_val_719_);
lean_dec(v_a_715_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_751_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___y_724_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_736_ = lean_name_eq(v_declName_701_, v___x_735_);
lean_dec(v_declName_701_);
if (v___x_736_ == 0)
{
lean_dec_ref(v_e_687_);
v___y_724_ = v_snd_710_;
goto v___jp_723_;
}
else
{
lean_object* v_dummy_737_; lean_object* v_nargs_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v_dummy_737_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_738_ = l_Lean_Expr_getAppNumArgs(v_e_687_);
lean_inc(v_nargs_738_);
v___x_739_ = lean_mk_array(v_nargs_738_, v_dummy_737_);
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_sub(v_nargs_738_, v___x_740_);
lean_dec(v_nargs_738_);
v___x_742_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_687_, v___x_739_, v___x_741_);
v___x_743_ = lean_unsigned_to_nat(2u);
v___x_744_ = lean_array_get_size(v___x_742_);
v___x_745_ = lean_nat_dec_lt(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_dec_ref(v___x_742_);
v___y_724_ = v_snd_710_;
goto v___jp_723_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_746_ = lean_array_fget(v___x_742_, v___x_743_);
lean_dec_ref(v___x_742_);
v___x_747_ = l_Lean_Expr_getAppFn(v___x_746_);
lean_dec(v___x_746_);
v___x_748_ = l_Lean_Expr_isConst(v___x_747_);
if (v___x_748_ == 0)
{
lean_dec_ref(v___x_747_);
v___y_724_ = v_snd_710_;
goto v___jp_723_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = l_Lean_Expr_constName_x21(v___x_747_);
lean_dec_ref(v___x_747_);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v_snd_710_);
v___y_724_ = v___x_750_;
goto v___jp_723_;
}
}
}
v___jp_723_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = l_Lean_Expr_headBeta(v_val_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_725_);
v___x_727_ = v___x_721_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_734_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_729_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v___y_724_);
lean_ctor_set(v___x_712_, 0, v___x_727_);
v___x_729_ = v___x_712_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___y_724_);
v___x_729_ = v_reuseFailAlloc_733_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_729_);
v___x_731_ = v___x_717_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_717_);
lean_dec(v_a_715_);
lean_del_object(v___x_712_);
lean_dec(v_declName_701_);
lean_dec_ref(v_e_687_);
v___y_695_ = v_snd_710_;
goto v___jp_694_;
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_del_object(v___x_712_);
lean_dec(v_snd_710_);
lean_dec(v_declName_701_);
lean_dec_ref(v_e_687_);
v_a_753_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_714_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_714_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_declName_701_);
lean_dec_ref(v_e_687_);
v_a_763_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_708_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_708_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_declName_701_);
lean_dec(v___y_688_);
lean_dec_ref(v_e_687_);
v_a_771_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_705_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_705_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___y_695_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Meta_expandCoe___lam__1(v_e_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0(lean_object* v_k_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v_b_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
lean_inc(v___y_794_);
lean_inc_ref(v___y_793_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
lean_inc(v___y_788_);
v___x_796_ = lean_apply_8(v_k_787_, v_b_790_, v___y_788_, v___y_789_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, lean_box(0));
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0___boxed(lean_object* v_k_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v_b_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0(v_k_797_, v___y_798_, v___y_799_, v_b_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_798_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(lean_object* v_name_807_, lean_object* v_type_808_, lean_object* v_val_809_, lean_object* v_k_810_, uint8_t v_nondep_811_, uint8_t v_kind_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___f_820_; lean_object* v___x_821_; 
lean_inc(v___y_813_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_820_, 0, v_k_810_);
lean_closure_set(v___f_820_, 1, v___y_813_);
lean_closure_set(v___f_820_, 2, v___y_814_);
v___x_821_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_807_, v_type_808_, v_val_809_, v___f_820_, v_nondep_811_, v_kind_812_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_a_830_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_821_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_821_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg___boxed(lean_object* v_name_838_, lean_object* v_type_839_, lean_object* v_val_840_, lean_object* v_k_841_, lean_object* v_nondep_842_, lean_object* v_kind_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v_nondep_boxed_851_; uint8_t v_kind_boxed_852_; lean_object* v_res_853_; 
v_nondep_boxed_851_ = lean_unbox(v_nondep_842_);
v_kind_boxed_852_ = lean_unbox(v_kind_843_);
v_res_853_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(v_name_838_, v_type_839_, v_val_840_, v_k_841_, v_nondep_boxed_851_, v_kind_boxed_852_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_844_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(lean_object* v_name_854_, uint8_t v_bi_855_, lean_object* v_type_856_, lean_object* v_k_857_, uint8_t v_kind_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___f_866_; lean_object* v___x_867_; 
lean_inc(v___y_859_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_866_, 0, v_k_857_);
lean_closure_set(v___f_866_, 1, v___y_859_);
lean_closure_set(v___f_866_, 2, v___y_860_);
v___x_867_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_854_, v_bi_855_, v_type_856_, v___f_866_, v_kind_858_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_867_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_867_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg___boxed(lean_object* v_name_884_, lean_object* v_bi_885_, lean_object* v_type_886_, lean_object* v_k_887_, lean_object* v_kind_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v_bi_boxed_896_; uint8_t v_kind_boxed_897_; lean_object* v_res_898_; 
v_bi_boxed_896_ = lean_unbox(v_bi_885_);
v_kind_boxed_897_ = lean_unbox(v_kind_888_);
v_res_898_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_name_884_, v_bi_boxed_896_, v_type_886_, v_k_887_, v_kind_boxed_897_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_889_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__2(lean_object* v___x_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_899_);
lean_ctor_set(v___x_906_, 1, v___y_900_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__2___boxed(lean_object* v___x_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__2(v___x_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30___redArg(lean_object* v_x_916_, lean_object* v_x_917_){
_start:
{
if (lean_obj_tag(v_x_917_) == 0)
{
return v_x_916_;
}
else
{
lean_object* v_key_918_; lean_object* v_value_919_; lean_object* v_tail_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_943_; 
v_key_918_ = lean_ctor_get(v_x_917_, 0);
v_value_919_ = lean_ctor_get(v_x_917_, 1);
v_tail_920_ = lean_ctor_get(v_x_917_, 2);
v_isSharedCheck_943_ = !lean_is_exclusive(v_x_917_);
if (v_isSharedCheck_943_ == 0)
{
v___x_922_ = v_x_917_;
v_isShared_923_ = v_isSharedCheck_943_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_tail_920_);
lean_inc(v_value_919_);
lean_inc(v_key_918_);
lean_dec(v_x_917_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_943_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; uint64_t v___x_925_; uint64_t v___x_926_; uint64_t v___x_927_; uint64_t v_fold_928_; uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v___x_931_; size_t v___x_932_; size_t v___x_933_; size_t v___x_934_; size_t v___x_935_; size_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_924_ = lean_array_get_size(v_x_916_);
v___x_925_ = l_Lean_ExprStructEq_hash(v_key_918_);
v___x_926_ = 32ULL;
v___x_927_ = lean_uint64_shift_right(v___x_925_, v___x_926_);
v_fold_928_ = lean_uint64_xor(v___x_925_, v___x_927_);
v___x_929_ = 16ULL;
v___x_930_ = lean_uint64_shift_right(v_fold_928_, v___x_929_);
v___x_931_ = lean_uint64_xor(v_fold_928_, v___x_930_);
v___x_932_ = lean_uint64_to_usize(v___x_931_);
v___x_933_ = lean_usize_of_nat(v___x_924_);
v___x_934_ = ((size_t)1ULL);
v___x_935_ = lean_usize_sub(v___x_933_, v___x_934_);
v___x_936_ = lean_usize_land(v___x_932_, v___x_935_);
v___x_937_ = lean_array_uget_borrowed(v_x_916_, v___x_936_);
lean_inc(v___x_937_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 2, v___x_937_);
v___x_939_ = v___x_922_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_key_918_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_value_919_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v___x_937_);
v___x_939_ = v_reuseFailAlloc_942_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; 
v___x_940_ = lean_array_uset(v_x_916_, v___x_936_, v___x_939_);
v_x_916_ = v___x_940_;
v_x_917_ = v_tail_920_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29___redArg(lean_object* v_i_944_, lean_object* v_source_945_, lean_object* v_target_946_){
_start:
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = lean_array_get_size(v_source_945_);
v___x_948_ = lean_nat_dec_lt(v_i_944_, v___x_947_);
if (v___x_948_ == 0)
{
lean_dec_ref(v_source_945_);
lean_dec(v_i_944_);
return v_target_946_;
}
else
{
lean_object* v_es_949_; lean_object* v___x_950_; lean_object* v_source_951_; lean_object* v_target_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_es_949_ = lean_array_fget(v_source_945_, v_i_944_);
v___x_950_ = lean_box(0);
v_source_951_ = lean_array_fset(v_source_945_, v_i_944_, v___x_950_);
v_target_952_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30___redArg(v_target_946_, v_es_949_);
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_add(v_i_944_, v___x_953_);
lean_dec(v_i_944_);
v_i_944_ = v___x_954_;
v_source_945_ = v_source_951_;
v_target_946_ = v_target_952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(lean_object* v_data_956_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_nbuckets_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_957_ = lean_array_get_size(v_data_956_);
v___x_958_ = lean_unsigned_to_nat(2u);
v_nbuckets_959_ = lean_nat_mul(v___x_957_, v___x_958_);
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_box(0);
v___x_962_ = lean_mk_array(v_nbuckets_959_, v___x_961_);
v___x_963_ = lean_array_propagate_mark(v_data_956_, v___x_962_);
v___x_964_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29___redArg(v___x_960_, v_data_956_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(lean_object* v_a_965_, lean_object* v_x_966_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg___boxed(lean_object* v_a_972_, lean_object* v_x_973_){
_start:
{
uint8_t v_res_974_; lean_object* v_r_975_; 
v_res_974_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(v_a_972_, v_x_973_);
lean_dec(v_x_973_);
lean_dec_ref(v_a_972_);
v_r_975_ = lean_box(v_res_974_);
return v_r_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28___redArg(lean_object* v_a_976_, lean_object* v_b_977_, lean_object* v_x_978_){
_start:
{
if (lean_obj_tag(v_x_978_) == 0)
{
lean_dec(v_b_977_);
lean_dec_ref(v_a_976_);
return v_x_978_;
}
else
{
lean_object* v_key_979_; lean_object* v_value_980_; lean_object* v_tail_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_993_; 
v_key_979_ = lean_ctor_get(v_x_978_, 0);
v_value_980_ = lean_ctor_get(v_x_978_, 1);
v_tail_981_ = lean_ctor_get(v_x_978_, 2);
v_isSharedCheck_993_ = !lean_is_exclusive(v_x_978_);
if (v_isSharedCheck_993_ == 0)
{
v___x_983_ = v_x_978_;
v_isShared_984_ = v_isSharedCheck_993_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_tail_981_);
lean_inc(v_value_980_);
lean_inc(v_key_979_);
lean_dec(v_x_978_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_993_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
uint8_t v___x_985_; 
v___x_985_ = l_Lean_ExprStructEq_beq(v_key_979_, v_a_976_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28___redArg(v_a_976_, v_b_977_, v_tail_981_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 2, v___x_986_);
v___x_988_ = v___x_983_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_key_979_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_value_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
else
{
lean_object* v___x_991_; 
lean_dec(v_value_980_);
lean_dec(v_key_979_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v_b_977_);
lean_ctor_set(v___x_983_, 0, v_a_976_);
v___x_991_ = v___x_983_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_976_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_b_977_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_tail_981_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(lean_object* v_m_994_, lean_object* v_a_995_, lean_object* v_b_996_){
_start:
{
lean_object* v_size_997_; lean_object* v_buckets_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1041_; 
v_size_997_ = lean_ctor_get(v_m_994_, 0);
v_buckets_998_ = lean_ctor_get(v_m_994_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_m_994_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1000_ = v_m_994_;
v_isShared_1001_ = v_isSharedCheck_1041_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_buckets_998_);
lean_inc(v_size_997_);
lean_dec(v_m_994_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1041_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; uint64_t v_fold_1006_; uint64_t v___x_1007_; uint64_t v___x_1008_; uint64_t v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; lean_object* v_bkt_1015_; uint8_t v___x_1016_; 
v___x_1002_ = lean_array_get_size(v_buckets_998_);
v___x_1003_ = l_Lean_ExprStructEq_hash(v_a_995_);
v___x_1004_ = 32ULL;
v___x_1005_ = lean_uint64_shift_right(v___x_1003_, v___x_1004_);
v_fold_1006_ = lean_uint64_xor(v___x_1003_, v___x_1005_);
v___x_1007_ = 16ULL;
v___x_1008_ = lean_uint64_shift_right(v_fold_1006_, v___x_1007_);
v___x_1009_ = lean_uint64_xor(v_fold_1006_, v___x_1008_);
v___x_1010_ = lean_uint64_to_usize(v___x_1009_);
v___x_1011_ = lean_usize_of_nat(v___x_1002_);
v___x_1012_ = ((size_t)1ULL);
v___x_1013_ = lean_usize_sub(v___x_1011_, v___x_1012_);
v___x_1014_ = lean_usize_land(v___x_1010_, v___x_1013_);
v_bkt_1015_ = lean_array_uget_borrowed(v_buckets_998_, v___x_1014_);
v___x_1016_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(v_a_995_, v_bkt_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v_size_x27_1018_; lean_object* v___x_1019_; lean_object* v_buckets_x27_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1017_ = lean_unsigned_to_nat(1u);
v_size_x27_1018_ = lean_nat_add(v_size_997_, v___x_1017_);
lean_dec(v_size_997_);
lean_inc(v_bkt_1015_);
v___x_1019_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1019_, 0, v_a_995_);
lean_ctor_set(v___x_1019_, 1, v_b_996_);
lean_ctor_set(v___x_1019_, 2, v_bkt_1015_);
v_buckets_x27_1020_ = lean_array_uset(v_buckets_998_, v___x_1014_, v___x_1019_);
v___x_1021_ = lean_unsigned_to_nat(4u);
v___x_1022_ = lean_nat_mul(v_size_x27_1018_, v___x_1021_);
v___x_1023_ = lean_unsigned_to_nat(3u);
v___x_1024_ = lean_nat_div(v___x_1022_, v___x_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_array_get_size(v_buckets_x27_1020_);
v___x_1026_ = lean_nat_dec_le(v___x_1024_, v___x_1025_);
lean_dec(v___x_1024_);
if (v___x_1026_ == 0)
{
lean_object* v_val_1027_; lean_object* v___x_1029_; 
v_val_1027_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_buckets_x27_1020_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 1, v_val_1027_);
lean_ctor_set(v___x_1000_, 0, v_size_x27_1018_);
v___x_1029_ = v___x_1000_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_size_x27_1018_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_val_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
else
{
lean_object* v___x_1032_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 1, v_buckets_x27_1020_);
lean_ctor_set(v___x_1000_, 0, v_size_x27_1018_);
v___x_1032_ = v___x_1000_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_size_x27_1018_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_buckets_x27_1020_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
else
{
lean_object* v___x_1034_; lean_object* v_buckets_x27_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
lean_inc(v_bkt_1015_);
v___x_1034_ = lean_box(0);
v_buckets_x27_1035_ = lean_array_uset(v_buckets_998_, v___x_1014_, v___x_1034_);
v___x_1036_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28___redArg(v_a_995_, v_b_996_, v_bkt_1015_);
v___x_1037_ = lean_array_uset(v_buckets_x27_1035_, v___x_1014_, v___x_1036_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 1, v___x_1037_);
v___x_1039_ = v___x_1000_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_size_997_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_1042_, lean_object* v_e_1043_, lean_object* v_fst_1044_){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1046_ = lean_st_ref_take(v_a_1042_);
v___x_1047_ = lean_box(0);
v___x_1048_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v___x_1046_, v_e_1043_, v_fst_1044_);
v___x_1049_ = lean_st_ref_put(v_a_1042_, v___x_1048_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_1050_, lean_object* v_e_1051_, lean_object* v_fst_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1050_, v_e_1051_, v_fst_1052_);
lean_dec(v_a_1050_);
return v_res_1054_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__3(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = l_Lean_maxRecDepthErrorMessage;
v___x_1061_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__4(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__3);
v___x_1063_ = l_Lean_MessageData_ofFormat(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__5(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__4);
v___x_1065_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__2));
v___x_1066_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v___x_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object* v_ref_1067_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___closed__5);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_ref_1067_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object* v_ref_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_ref_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_x_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___y_1084_; lean_object* v_toCold_1101_; lean_object* v_currRecDepth_1102_; lean_object* v_ref_1103_; uint16_t v_optionFlags_1104_; uint8_t v_suppressElabErrors_1105_; uint8_t v_checkDeprecated_1106_; uint8_t v_isRecordingDeps_1107_; lean_object* v_maxRecDepth_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_toCold_1101_ = lean_ctor_get(v___y_1080_, 0);
v_currRecDepth_1102_ = lean_ctor_get(v___y_1080_, 1);
v_ref_1103_ = lean_ctor_get(v___y_1080_, 2);
v_optionFlags_1104_ = lean_ctor_get_uint16(v___y_1080_, sizeof(void*)*3);
v_suppressElabErrors_1105_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*3 + 2);
v_checkDeprecated_1106_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1107_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*3 + 4);
v_maxRecDepth_1113_ = lean_ctor_get(v_toCold_1101_, 3);
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = lean_nat_dec_eq(v_maxRecDepth_1113_, v___x_1114_);
if (v___x_1115_ == 0)
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_nat_dec_eq(v_currRecDepth_1102_, v_maxRecDepth_1113_);
if (v___x_1116_ == 0)
{
goto v___jp_1108_;
}
else
{
lean_object* v___x_1117_; 
lean_dec(v___y_1077_);
lean_dec_ref(v_x_1075_);
lean_inc(v_ref_1103_);
v___x_1117_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_ref_1103_);
v___y_1084_ = v___x_1117_;
goto v___jp_1083_;
}
}
else
{
goto v___jp_1108_;
}
v___jp_1083_:
{
if (lean_obj_tag(v___y_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1085_ = lean_ctor_get(v___y_1084_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___y_1084_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___y_1084_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___y_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___y_1084_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___y_1084_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___y_1084_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___y_1084_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
v___jp_1108_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_nat_add(v_currRecDepth_1102_, v___x_1109_);
lean_inc(v_ref_1103_);
lean_inc_ref(v_toCold_1101_);
v___x_1111_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1111_, 0, v_toCold_1101_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
lean_ctor_set(v___x_1111_, 2, v_ref_1103_);
lean_ctor_set_uint16(v___x_1111_, sizeof(void*)*3, v_optionFlags_1104_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*3 + 2, v_suppressElabErrors_1105_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*3 + 3, v_checkDeprecated_1106_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*3 + 4, v_isRecordingDeps_1107_);
lean_inc(v___y_1081_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc(v___y_1076_);
v___x_1112_ = lean_apply_7(v_x_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___x_1111_, v___y_1081_, lean_box(0));
v___y_1084_ = v___x_1112_;
goto v___jp_1083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg___boxed(lean_object* v_x_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_x_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1119_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_a_1127_, lean_object* v_x_1128_){
_start:
{
if (lean_obj_tag(v_x_1128_) == 0)
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_box(0);
return v___x_1129_;
}
else
{
lean_object* v_key_1130_; lean_object* v_value_1131_; lean_object* v_tail_1132_; uint8_t v___x_1133_; 
v_key_1130_ = lean_ctor_get(v_x_1128_, 0);
v_value_1131_ = lean_ctor_get(v_x_1128_, 1);
v_tail_1132_ = lean_ctor_get(v_x_1128_, 2);
v___x_1133_ = l_Lean_ExprStructEq_beq(v_key_1130_, v_a_1127_);
if (v___x_1133_ == 0)
{
v_x_1128_ = v_tail_1132_;
goto _start;
}
else
{
lean_object* v___x_1135_; 
lean_inc(v_value_1131_);
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_value_1131_);
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13___redArg___boxed(lean_object* v_a_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13___redArg(v_a_1136_, v_x_1137_);
lean_dec(v_x_1137_);
lean_dec_ref(v_a_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___redArg(lean_object* v_m_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_buckets_1141_; lean_object* v___x_1142_; uint64_t v___x_1143_; uint64_t v___x_1144_; uint64_t v___x_1145_; uint64_t v_fold_1146_; uint64_t v___x_1147_; uint64_t v___x_1148_; uint64_t v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_buckets_1141_ = lean_ctor_get(v_m_1139_, 1);
v___x_1142_ = lean_array_get_size(v_buckets_1141_);
v___x_1143_ = l_Lean_ExprStructEq_hash(v_a_1140_);
v___x_1144_ = 32ULL;
v___x_1145_ = lean_uint64_shift_right(v___x_1143_, v___x_1144_);
v_fold_1146_ = lean_uint64_xor(v___x_1143_, v___x_1145_);
v___x_1147_ = 16ULL;
v___x_1148_ = lean_uint64_shift_right(v_fold_1146_, v___x_1147_);
v___x_1149_ = lean_uint64_xor(v_fold_1146_, v___x_1148_);
v___x_1150_ = lean_uint64_to_usize(v___x_1149_);
v___x_1151_ = lean_usize_of_nat(v___x_1142_);
v___x_1152_ = ((size_t)1ULL);
v___x_1153_ = lean_usize_sub(v___x_1151_, v___x_1152_);
v___x_1154_ = lean_usize_land(v___x_1150_, v___x_1153_);
v___x_1155_ = lean_array_uget_borrowed(v_buckets_1141_, v___x_1154_);
v___x_1156_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13___redArg(v_a_1140_, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_m_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___redArg(v_m_1157_, v_a_1158_);
lean_dec_ref(v_a_1158_);
lean_dec_ref(v_m_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_apply_1(v_x_1161_, lean_box(0));
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___y_1162_);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_x_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1171_, v_x_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1180_, lean_object* v_pre_1181_, lean_object* v_post_1182_, lean_object* v_usedLetOnly_1183_, lean_object* v_skipConstInApp_1184_, lean_object* v_skipInstances_1185_, lean_object* v_postApp_1186_, lean_object* v_body_1187_, lean_object* v_x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v_usedLetOnly_boxed_1196_; uint8_t v_skipConstInApp_boxed_1197_; uint8_t v_skipInstances_boxed_1198_; lean_object* v_res_1199_; 
v_usedLetOnly_boxed_1196_ = lean_unbox(v_usedLetOnly_1183_);
v_skipConstInApp_boxed_1197_ = lean_unbox(v_skipConstInApp_1184_);
v_skipInstances_boxed_1198_ = lean_unbox(v_skipInstances_1185_);
v_res_1199_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1180_, v_pre_1181_, v_post_1182_, v_usedLetOnly_boxed_1196_, v_skipConstInApp_boxed_1197_, v_skipInstances_boxed_1198_, v_postApp_1186_, v_body_1187_, v_x_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1189_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1203_, lean_object* v_pre_1204_, lean_object* v_post_1205_, uint8_t v_usedLetOnly_1206_, uint8_t v_skipConstInApp_1207_, uint8_t v_skipInstances_1208_, lean_object* v_postApp_1209_, lean_object* v_body_1210_, lean_object* v_x_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_array_push(v_fvars_1203_, v_x_1211_);
v___x_1220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1204_, v_post_1205_, v_usedLetOnly_1206_, v_skipConstInApp_1207_, v_skipInstances_1208_, v_postApp_1209_, v___x_1219_, v_body_1210_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1221_, lean_object* v_pre_1222_, lean_object* v_post_1223_, lean_object* v_usedLetOnly_1224_, lean_object* v_skipConstInApp_1225_, lean_object* v_skipInstances_1226_, lean_object* v_postApp_1227_, lean_object* v_body_1228_, lean_object* v_x_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v_usedLetOnly_boxed_1237_; uint8_t v_skipConstInApp_boxed_1238_; uint8_t v_skipInstances_boxed_1239_; lean_object* v_res_1240_; 
v_usedLetOnly_boxed_1237_ = lean_unbox(v_usedLetOnly_1224_);
v_skipConstInApp_boxed_1238_ = lean_unbox(v_skipConstInApp_1225_);
v_skipInstances_boxed_1239_ = lean_unbox(v_skipInstances_1226_);
v_res_1240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1221_, v_pre_1222_, v_post_1223_, v_usedLetOnly_boxed_1237_, v_skipConstInApp_boxed_1238_, v_skipInstances_boxed_1239_, v_postApp_1227_, v_body_1228_, v_x_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1230_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_pre_1241_, lean_object* v_post_1242_, uint8_t v_usedLetOnly_1243_, uint8_t v_skipConstInApp_1244_, uint8_t v_skipInstances_1245_, lean_object* v_postApp_1246_, lean_object* v_e_1247_, lean_object* v_a_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
lean_inc_ref(v_post_1242_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
lean_inc(v___y_1251_);
lean_inc_ref(v___y_1250_);
lean_inc_ref(v_e_1247_);
v___x_1255_ = lean_apply_7(v_post_1242_, v_e_1247_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, lean_box(0));
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1287_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1258_ = v___x_1255_;
v_isShared_1259_ = v_isSharedCheck_1287_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1287_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_fst_1260_; lean_object* v_snd_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1286_; 
v_fst_1260_ = lean_ctor_get(v_a_1256_, 0);
v_snd_1261_ = lean_ctor_get(v_a_1256_, 1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_a_1256_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1263_ = v_a_1256_;
v_isShared_1264_ = v_isSharedCheck_1286_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_snd_1261_);
lean_inc(v_fst_1260_);
lean_dec(v_a_1256_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1286_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___y_1266_; 
switch(lean_obj_tag(v_fst_1260_))
{
case 0:
{
lean_object* v_e_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1281_; 
lean_del_object(v___x_1263_);
lean_del_object(v___x_1258_);
lean_dec_ref(v_e_1247_);
lean_dec_ref(v_postApp_1246_);
lean_dec_ref(v_post_1242_);
lean_dec_ref(v_pre_1241_);
v_e_1273_ = lean_ctor_get(v_fst_1260_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_fst_1260_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1275_ = v_fst_1260_;
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_e_1273_);
lean_dec(v_fst_1260_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v_e_1273_);
lean_ctor_set(v___x_1277_, 1, v_snd_1261_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1277_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
case 1:
{
lean_object* v_e_1282_; lean_object* v___x_1283_; 
lean_del_object(v___x_1263_);
lean_del_object(v___x_1258_);
lean_dec_ref(v_e_1247_);
v_e_1282_ = lean_ctor_get(v_fst_1260_, 0);
lean_inc_ref(v_e_1282_);
lean_dec_ref_known(v_fst_1260_, 1);
v___x_1283_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1241_, v_post_1242_, v_usedLetOnly_1243_, v_skipConstInApp_1244_, v_skipInstances_1245_, v_postApp_1246_, v_e_1282_, v_a_1248_, v_snd_1261_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1283_;
}
default: 
{
lean_object* v_e_x3f_1284_; 
lean_dec_ref(v_postApp_1246_);
lean_dec_ref(v_post_1242_);
lean_dec_ref(v_pre_1241_);
v_e_x3f_1284_ = lean_ctor_get(v_fst_1260_, 0);
lean_inc(v_e_x3f_1284_);
lean_dec_ref_known(v_fst_1260_, 1);
if (lean_obj_tag(v_e_x3f_1284_) == 0)
{
v___y_1266_ = v_e_1247_;
goto v___jp_1265_;
}
else
{
lean_object* v_val_1285_; 
lean_dec_ref(v_e_1247_);
v_val_1285_ = lean_ctor_get(v_e_x3f_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v_e_x3f_1284_, 1);
v___y_1266_ = v_val_1285_;
goto v___jp_1265_;
}
}
}
v___jp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___y_1266_);
v___x_1268_ = v___x_1263_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___y_1266_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_snd_1261_);
v___x_1268_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1268_);
v___x_1270_ = v___x_1258_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_e_1247_);
lean_dec_ref(v_postApp_1246_);
lean_dec_ref(v_post_1242_);
lean_dec_ref(v_pre_1241_);
v_a_1288_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1255_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1255_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1296_, lean_object* v_post_1297_, uint8_t v_usedLetOnly_1298_, uint8_t v_skipConstInApp_1299_, uint8_t v_skipInstances_1300_, lean_object* v_postApp_1301_, lean_object* v_fvars_1302_, lean_object* v_e_1303_, lean_object* v_a_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
if (lean_obj_tag(v_e_1303_) == 6)
{
lean_object* v_binderName_1311_; lean_object* v_binderType_1312_; lean_object* v_body_1313_; uint8_t v_binderInfo_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___f_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_binderName_1311_ = lean_ctor_get(v_e_1303_, 0);
lean_inc(v_binderName_1311_);
v_binderType_1312_ = lean_ctor_get(v_e_1303_, 1);
lean_inc_ref(v_binderType_1312_);
v_body_1313_ = lean_ctor_get(v_e_1303_, 2);
lean_inc_ref(v_body_1313_);
v_binderInfo_1314_ = lean_ctor_get_uint8(v_e_1303_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1303_, 3);
v___x_1315_ = lean_box(v_usedLetOnly_1298_);
v___x_1316_ = lean_box(v_skipConstInApp_1299_);
v___x_1317_ = lean_box(v_skipInstances_1300_);
lean_inc_ref(v_postApp_1301_);
lean_inc_ref(v_post_1297_);
lean_inc_ref(v_pre_1296_);
lean_inc_ref(v_fvars_1302_);
v___f_1318_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 16, 8);
lean_closure_set(v___f_1318_, 0, v_fvars_1302_);
lean_closure_set(v___f_1318_, 1, v_pre_1296_);
lean_closure_set(v___f_1318_, 2, v_post_1297_);
lean_closure_set(v___f_1318_, 3, v___x_1315_);
lean_closure_set(v___f_1318_, 4, v___x_1316_);
lean_closure_set(v___f_1318_, 5, v___x_1317_);
lean_closure_set(v___f_1318_, 6, v_postApp_1301_);
lean_closure_set(v___f_1318_, 7, v_body_1313_);
v___x_1319_ = lean_expr_instantiate_rev(v_binderType_1312_, v_fvars_1302_);
lean_dec_ref(v_fvars_1302_);
lean_dec_ref(v_binderType_1312_);
v___x_1320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1296_, v_post_1297_, v_usedLetOnly_1298_, v_skipConstInApp_1299_, v_skipInstances_1300_, v_postApp_1301_, v___x_1319_, v_a_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v_fst_1322_; lean_object* v_snd_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v_fst_1322_ = lean_ctor_get(v_a_1321_, 0);
lean_inc(v_fst_1322_);
v_snd_1323_ = lean_ctor_get(v_a_1321_, 1);
lean_inc(v_snd_1323_);
lean_dec(v_a_1321_);
v___x_1324_ = 0;
v___x_1325_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_binderName_1311_, v_binderInfo_1314_, v_fst_1322_, v___f_1318_, v___x_1324_, v_a_1304_, v_snd_1323_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1325_;
}
else
{
lean_dec_ref(v___f_1318_);
lean_dec(v_binderName_1311_);
return v___x_1320_;
}
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_expr_instantiate_rev(v_e_1303_, v_fvars_1302_);
lean_dec_ref(v_e_1303_);
lean_inc_ref(v_postApp_1301_);
lean_inc_ref(v_post_1297_);
lean_inc_ref(v_pre_1296_);
v___x_1327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1296_, v_post_1297_, v_usedLetOnly_1298_, v_skipConstInApp_1299_, v_skipInstances_1300_, v_postApp_1301_, v___x_1326_, v_a_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v_fst_1329_; lean_object* v_snd_1330_; uint8_t v___x_1331_; uint8_t v___x_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v_fst_1329_ = lean_ctor_get(v_a_1328_, 0);
lean_inc(v_fst_1329_);
v_snd_1330_ = lean_ctor_get(v_a_1328_, 1);
lean_inc(v_snd_1330_);
lean_dec(v_a_1328_);
v___x_1331_ = 0;
v___x_1332_ = 1;
v___x_1333_ = 1;
v___x_1334_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1302_, v_fst_1329_, v___x_1331_, v_usedLetOnly_1298_, v___x_1331_, v___x_1332_, v___x_1333_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec_ref(v_fvars_1302_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1336_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1334_, 1);
v___x_1336_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1296_, v_post_1297_, v_usedLetOnly_1298_, v_skipConstInApp_1299_, v_skipInstances_1300_, v_postApp_1301_, v_a_1335_, v_a_1304_, v_snd_1330_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1336_;
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v_snd_1330_);
lean_dec_ref(v_postApp_1301_);
lean_dec_ref(v_post_1297_);
lean_dec_ref(v_pre_1296_);
v_a_1337_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1334_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1334_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1302_);
lean_dec_ref(v_postApp_1301_);
lean_dec_ref(v_post_1297_);
lean_dec_ref(v_pre_1296_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(lean_object* v_fvars_1345_, lean_object* v_pre_1346_, lean_object* v_post_1347_, uint8_t v_usedLetOnly_1348_, uint8_t v_skipConstInApp_1349_, uint8_t v_skipInstances_1350_, lean_object* v_postApp_1351_, lean_object* v_body_1352_, lean_object* v_x_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_array_push(v_fvars_1345_, v_x_1353_);
v___x_1362_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1346_, v_post_1347_, v_usedLetOnly_1348_, v_skipConstInApp_1349_, v_skipInstances_1350_, v_postApp_1351_, v___x_1361_, v_body_1352_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed(lean_object* v_fvars_1363_, lean_object* v_pre_1364_, lean_object* v_post_1365_, lean_object* v_usedLetOnly_1366_, lean_object* v_skipConstInApp_1367_, lean_object* v_skipInstances_1368_, lean_object* v_postApp_1369_, lean_object* v_body_1370_, lean_object* v_x_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
uint8_t v_usedLetOnly_boxed_1379_; uint8_t v_skipConstInApp_boxed_1380_; uint8_t v_skipInstances_boxed_1381_; lean_object* v_res_1382_; 
v_usedLetOnly_boxed_1379_ = lean_unbox(v_usedLetOnly_1366_);
v_skipConstInApp_boxed_1380_ = lean_unbox(v_skipConstInApp_1367_);
v_skipInstances_boxed_1381_ = lean_unbox(v_skipInstances_1368_);
v_res_1382_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(v_fvars_1363_, v_pre_1364_, v_post_1365_, v_usedLetOnly_boxed_1379_, v_skipConstInApp_boxed_1380_, v_skipInstances_boxed_1381_, v_postApp_1369_, v_body_1370_, v_x_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1372_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(lean_object* v_pre_1383_, lean_object* v_post_1384_, uint8_t v_usedLetOnly_1385_, uint8_t v_skipConstInApp_1386_, uint8_t v_skipInstances_1387_, lean_object* v_postApp_1388_, lean_object* v_fvars_1389_, lean_object* v_e_1390_, lean_object* v_a_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
if (lean_obj_tag(v_e_1390_) == 8)
{
lean_object* v_declName_1398_; lean_object* v_type_1399_; lean_object* v_value_1400_; lean_object* v_body_1401_; uint8_t v_nondep_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_declName_1398_ = lean_ctor_get(v_e_1390_, 0);
lean_inc(v_declName_1398_);
v_type_1399_ = lean_ctor_get(v_e_1390_, 1);
lean_inc_ref(v_type_1399_);
v_value_1400_ = lean_ctor_get(v_e_1390_, 2);
lean_inc_ref(v_value_1400_);
v_body_1401_ = lean_ctor_get(v_e_1390_, 3);
lean_inc_ref(v_body_1401_);
v_nondep_1402_ = lean_ctor_get_uint8(v_e_1390_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1390_, 4);
v___x_1403_ = lean_box(v_usedLetOnly_1385_);
v___x_1404_ = lean_box(v_skipConstInApp_1386_);
v___x_1405_ = lean_box(v_skipInstances_1387_);
lean_inc_ref_n(v_postApp_1388_, 2);
lean_inc_ref_n(v_post_1384_, 2);
lean_inc_ref_n(v_pre_1383_, 2);
lean_inc_ref(v_fvars_1389_);
v___f_1406_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed), 16, 8);
lean_closure_set(v___f_1406_, 0, v_fvars_1389_);
lean_closure_set(v___f_1406_, 1, v_pre_1383_);
lean_closure_set(v___f_1406_, 2, v_post_1384_);
lean_closure_set(v___f_1406_, 3, v___x_1403_);
lean_closure_set(v___f_1406_, 4, v___x_1404_);
lean_closure_set(v___f_1406_, 5, v___x_1405_);
lean_closure_set(v___f_1406_, 6, v_postApp_1388_);
lean_closure_set(v___f_1406_, 7, v_body_1401_);
v___x_1407_ = lean_expr_instantiate_rev(v_type_1399_, v_fvars_1389_);
lean_dec_ref(v_type_1399_);
v___x_1408_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1383_, v_post_1384_, v_usedLetOnly_1385_, v_skipConstInApp_1386_, v_skipInstances_1387_, v_postApp_1388_, v___x_1407_, v_a_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v_fst_1410_; lean_object* v_snd_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v_fst_1410_ = lean_ctor_get(v_a_1409_, 0);
lean_inc(v_fst_1410_);
v_snd_1411_ = lean_ctor_get(v_a_1409_, 1);
lean_inc(v_snd_1411_);
lean_dec(v_a_1409_);
v___x_1412_ = lean_expr_instantiate_rev(v_value_1400_, v_fvars_1389_);
lean_dec_ref(v_fvars_1389_);
lean_dec_ref(v_value_1400_);
v___x_1413_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1383_, v_post_1384_, v_usedLetOnly_1385_, v_skipConstInApp_1386_, v_skipInstances_1387_, v_postApp_1388_, v___x_1412_, v_a_1391_, v_snd_1411_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v_fst_1415_; lean_object* v_snd_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v_fst_1415_ = lean_ctor_get(v_a_1414_, 0);
lean_inc(v_fst_1415_);
v_snd_1416_ = lean_ctor_get(v_a_1414_, 1);
lean_inc(v_snd_1416_);
lean_dec(v_a_1414_);
v___x_1417_ = 0;
v___x_1418_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(v_declName_1398_, v_fst_1410_, v_fst_1415_, v___f_1406_, v_nondep_1402_, v___x_1417_, v_a_1391_, v_snd_1416_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1418_;
}
else
{
lean_dec(v_fst_1410_);
lean_dec_ref(v___f_1406_);
lean_dec(v_declName_1398_);
return v___x_1413_;
}
}
else
{
lean_dec_ref(v___f_1406_);
lean_dec_ref(v_value_1400_);
lean_dec(v_declName_1398_);
lean_dec_ref(v_fvars_1389_);
lean_dec_ref(v_postApp_1388_);
lean_dec_ref(v_post_1384_);
lean_dec_ref(v_pre_1383_);
return v___x_1408_;
}
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_expr_instantiate_rev(v_e_1390_, v_fvars_1389_);
lean_dec_ref(v_e_1390_);
lean_inc_ref(v_postApp_1388_);
lean_inc_ref(v_post_1384_);
lean_inc_ref(v_pre_1383_);
v___x_1420_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1383_, v_post_1384_, v_usedLetOnly_1385_, v_skipConstInApp_1386_, v_skipInstances_1387_, v_postApp_1388_, v___x_1419_, v_a_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v_fst_1422_; lean_object* v_snd_1423_; uint8_t v___x_1424_; uint8_t v___x_1425_; lean_object* v___x_1426_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v_fst_1422_ = lean_ctor_get(v_a_1421_, 0);
lean_inc(v_fst_1422_);
v_snd_1423_ = lean_ctor_get(v_a_1421_, 1);
lean_inc(v_snd_1423_);
lean_dec(v_a_1421_);
v___x_1424_ = 0;
v___x_1425_ = 1;
v___x_1426_ = l_Lean_Meta_mkLetFVars(v_fvars_1389_, v_fst_1422_, v_usedLetOnly_1385_, v___x_1424_, v___x_1425_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec_ref(v_fvars_1389_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1383_, v_post_1384_, v_usedLetOnly_1385_, v_skipConstInApp_1386_, v_skipInstances_1387_, v_postApp_1388_, v_a_1427_, v_a_1391_, v_snd_1423_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1428_;
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v_snd_1423_);
lean_dec_ref(v_postApp_1388_);
lean_dec_ref(v_post_1384_);
lean_dec_ref(v_pre_1383_);
v_a_1429_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1426_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1426_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1389_);
lean_dec_ref(v_postApp_1388_);
lean_dec_ref(v_post_1384_);
lean_dec_ref(v_pre_1383_);
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_pre_1437_, lean_object* v_post_1438_, uint8_t v_usedLetOnly_1439_, uint8_t v_skipConstInApp_1440_, uint8_t v_skipInstances_1441_, lean_object* v_postApp_1442_, size_t v_sz_1443_, size_t v_i_1444_, lean_object* v_bs_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_usize_dec_lt(v_i_1444_, v_sz_1443_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec_ref(v_postApp_1442_);
lean_dec_ref(v_post_1438_);
lean_dec_ref(v_pre_1437_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_bs_1445_);
lean_ctor_set(v___x_1454_, 1, v___y_1447_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
else
{
lean_object* v_v_1456_; lean_object* v___x_1457_; lean_object* v_bs_x27_1458_; lean_object* v___x_1459_; 
v_v_1456_ = lean_array_uget(v_bs_1445_, v_i_1444_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v_bs_x27_1458_ = lean_array_uset(v_bs_1445_, v_i_1444_, v___x_1457_);
lean_inc_ref(v_postApp_1442_);
lean_inc_ref(v_post_1438_);
lean_inc_ref(v_pre_1437_);
v___x_1459_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1437_, v_post_1438_, v_usedLetOnly_1439_, v_skipConstInApp_1440_, v_skipInstances_1441_, v_postApp_1442_, v_v_1456_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v_fst_1461_; lean_object* v_snd_1462_; size_t v___x_1463_; size_t v___x_1464_; lean_object* v___x_1465_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v_fst_1461_ = lean_ctor_get(v_a_1460_, 0);
lean_inc(v_fst_1461_);
v_snd_1462_ = lean_ctor_get(v_a_1460_, 1);
lean_inc(v_snd_1462_);
lean_dec(v_a_1460_);
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = lean_usize_add(v_i_1444_, v___x_1463_);
v___x_1465_ = lean_array_uset(v_bs_x27_1458_, v_i_1444_, v_fst_1461_);
v_i_1444_ = v___x_1464_;
v_bs_1445_ = v___x_1465_;
v___y_1447_ = v_snd_1462_;
goto _start;
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v_bs_x27_1458_);
lean_dec_ref(v_postApp_1442_);
lean_dec_ref(v_post_1438_);
lean_dec_ref(v_pre_1437_);
v_a_1467_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1459_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1459_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__0(lean_object* v_pre_1475_, lean_object* v_post_1476_, uint8_t v_usedLetOnly_1477_, uint8_t v_skipConstInApp_1478_, uint8_t v_skipInstances_1479_, lean_object* v_postApp_1480_, lean_object* v___x_1481_, lean_object* v___y_1482_, lean_object* v_b_1483_, lean_object* v_a_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1475_, v_post_1476_, v_usedLetOnly_1477_, v_skipConstInApp_1478_, v_skipInstances_1479_, v_postApp_1480_, v___x_1481_, v___y_1482_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1510_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1510_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1510_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1509_; 
v_fst_1496_ = lean_ctor_get(v_a_1492_, 0);
v_snd_1497_ = lean_ctor_get(v_a_1492_, 1);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_a_1492_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1499_ = v_a_1492_;
v_isShared_1500_ = v_isSharedCheck_1509_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_snd_1497_);
lean_inc(v_fst_1496_);
lean_dec(v_a_1492_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1509_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1501_ = lean_array_fset(v_b_1483_, v_a_1484_, v_fst_1496_);
v___x_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1502_);
v___x_1504_ = v___x_1499_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_snd_1497_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1504_);
v___x_1506_ = v___x_1494_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v_b_1483_);
v_a_1511_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1491_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1491_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1519_, lean_object* v_post_1520_, lean_object* v_usedLetOnly_1521_, lean_object* v_skipConstInApp_1522_, lean_object* v_skipInstances_1523_, lean_object* v_postApp_1524_, lean_object* v___x_1525_, lean_object* v___y_1526_, lean_object* v_b_1527_, lean_object* v_a_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v_usedLetOnly_boxed_1535_; uint8_t v_skipConstInApp_boxed_1536_; uint8_t v_skipInstances_boxed_1537_; lean_object* v_res_1538_; 
v_usedLetOnly_boxed_1535_ = lean_unbox(v_usedLetOnly_1521_);
v_skipConstInApp_boxed_1536_ = lean_unbox(v_skipConstInApp_1522_);
v_skipInstances_boxed_1537_ = lean_unbox(v_skipInstances_1523_);
v_res_1538_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__0(v_pre_1519_, v_post_1520_, v_usedLetOnly_boxed_1535_, v_skipConstInApp_boxed_1536_, v_skipInstances_boxed_1537_, v_postApp_1524_, v___x_1525_, v___y_1526_, v_b_1527_, v_a_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v_a_1528_);
lean_dec(v___y_1526_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(lean_object* v_upperBound_1539_, lean_object* v___x_1540_, lean_object* v_pre_1541_, lean_object* v_post_1542_, uint8_t v_usedLetOnly_1543_, uint8_t v_skipConstInApp_1544_, uint8_t v_skipInstances_1545_, lean_object* v_postApp_1546_, lean_object* v_a_1547_, lean_object* v_b_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___y_1557_; uint8_t v___x_1591_; 
v___x_1591_ = lean_nat_dec_lt(v_a_1547_, v_upperBound_1539_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec(v_a_1547_);
lean_dec_ref(v_postApp_1546_);
lean_dec_ref(v_post_1542_);
lean_dec_ref(v_pre_1541_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_b_1548_);
lean_ctor_set(v___x_1592_, 1, v___y_1550_);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1594_ = lean_array_fget_borrowed(v_b_1548_, v_a_1547_);
v___x_1595_ = lean_array_get_size(v___x_1540_);
v___x_1596_ = lean_nat_dec_lt(v_a_1547_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___f_1600_; 
lean_inc(v___x_1594_);
v___x_1597_ = lean_box(v_usedLetOnly_1543_);
v___x_1598_ = lean_box(v_skipConstInApp_1544_);
v___x_1599_ = lean_box(v_skipInstances_1545_);
lean_inc(v_a_1547_);
lean_inc(v___y_1549_);
lean_inc_ref(v_postApp_1546_);
lean_inc_ref(v_post_1542_);
lean_inc_ref(v_pre_1541_);
v___f_1600_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1600_, 0, v_pre_1541_);
lean_closure_set(v___f_1600_, 1, v_post_1542_);
lean_closure_set(v___f_1600_, 2, v___x_1597_);
lean_closure_set(v___f_1600_, 3, v___x_1598_);
lean_closure_set(v___f_1600_, 4, v___x_1599_);
lean_closure_set(v___f_1600_, 5, v_postApp_1546_);
lean_closure_set(v___f_1600_, 6, v___x_1594_);
lean_closure_set(v___f_1600_, 7, v___y_1549_);
lean_closure_set(v___f_1600_, 8, v_b_1548_);
lean_closure_set(v___f_1600_, 9, v_a_1547_);
v___y_1557_ = v___f_1600_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1601_; uint8_t v_isInstance_1602_; 
v___x_1601_ = lean_array_fget_borrowed(v___x_1540_, v_a_1547_);
v_isInstance_1602_ = lean_ctor_get_uint8(v___x_1601_, sizeof(void*)*1 + 4);
if (v_isInstance_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___f_1606_; 
lean_inc(v___x_1594_);
v___x_1603_ = lean_box(v_usedLetOnly_1543_);
v___x_1604_ = lean_box(v_skipConstInApp_1544_);
v___x_1605_ = lean_box(v_skipInstances_1545_);
lean_inc(v_a_1547_);
lean_inc(v___y_1549_);
lean_inc_ref(v_postApp_1546_);
lean_inc_ref(v_post_1542_);
lean_inc_ref(v_pre_1541_);
v___f_1606_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1606_, 0, v_pre_1541_);
lean_closure_set(v___f_1606_, 1, v_post_1542_);
lean_closure_set(v___f_1606_, 2, v___x_1603_);
lean_closure_set(v___f_1606_, 3, v___x_1604_);
lean_closure_set(v___f_1606_, 4, v___x_1605_);
lean_closure_set(v___f_1606_, 5, v_postApp_1546_);
lean_closure_set(v___f_1606_, 6, v___x_1594_);
lean_closure_set(v___f_1606_, 7, v___y_1549_);
lean_closure_set(v___f_1606_, 8, v_b_1548_);
lean_closure_set(v___f_1606_, 9, v_a_1547_);
v___y_1557_ = v___f_1606_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1607_; lean_object* v___f_1608_; 
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v_b_1548_);
v___f_1608_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1608_, 0, v___x_1607_);
v___y_1557_ = v___f_1608_;
goto v___jp_1556_;
}
}
}
v___jp_1556_:
{
lean_object* v___x_1558_; 
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
v___x_1558_ = lean_apply_6(v___y_1557_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1582_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1582_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1582_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_fst_1563_; 
v_fst_1563_ = lean_ctor_get(v_a_1559_, 0);
lean_inc(v_fst_1563_);
if (lean_obj_tag(v_fst_1563_) == 0)
{
lean_object* v_snd_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v_a_1547_);
lean_dec_ref(v_postApp_1546_);
lean_dec_ref(v_post_1542_);
lean_dec_ref(v_pre_1541_);
v_snd_1564_ = lean_ctor_get(v_a_1559_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_a_1559_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_a_1559_, 0);
lean_dec(v_unused_1576_);
v___x_1566_ = v_a_1559_;
v_isShared_1567_ = v_isSharedCheck_1575_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_snd_1564_);
lean_dec(v_a_1559_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1575_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_a_1568_; lean_object* v___x_1570_; 
v_a_1568_ = lean_ctor_get(v_fst_1563_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v_fst_1563_, 1);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v_a_1568_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_snd_1564_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1570_);
v___x_1572_ = v___x_1561_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_snd_1577_; lean_object* v_a_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_del_object(v___x_1561_);
v_snd_1577_ = lean_ctor_get(v_a_1559_, 1);
lean_inc(v_snd_1577_);
lean_dec(v_a_1559_);
v_a_1578_ = lean_ctor_get(v_fst_1563_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v_fst_1563_, 1);
v___x_1579_ = lean_unsigned_to_nat(1u);
v___x_1580_ = lean_nat_add(v_a_1547_, v___x_1579_);
lean_dec(v_a_1547_);
v_a_1547_ = v___x_1580_;
v_b_1548_ = v_a_1578_;
v___y_1550_ = v_snd_1577_;
goto _start;
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_a_1547_);
lean_dec_ref(v_postApp_1546_);
lean_dec_ref(v_post_1542_);
lean_dec_ref(v_pre_1541_);
v_a_1583_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1558_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1558_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(uint8_t v_skipInstances_1609_, lean_object* v_pre_1610_, lean_object* v_post_1611_, uint8_t v_usedLetOnly_1612_, uint8_t v_skipConstInApp_1613_, lean_object* v_postApp_1614_, lean_object* v___y_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_f_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; 
if (lean_obj_tag(v_x_1616_) == 5)
{
lean_object* v_fn_1690_; lean_object* v_arg_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_fn_1690_ = lean_ctor_get(v_x_1616_, 0);
lean_inc_ref(v_fn_1690_);
v_arg_1691_ = lean_ctor_get(v_x_1616_, 1);
lean_inc_ref(v_arg_1691_);
lean_dec_ref_known(v_x_1616_, 2);
v___x_1692_ = lean_array_set(v_x_1617_, v_x_1618_, v_arg_1691_);
v___x_1693_ = lean_unsigned_to_nat(1u);
v___x_1694_ = lean_nat_sub(v_x_1618_, v___x_1693_);
lean_dec(v_x_1618_);
v_x_1616_ = v_fn_1690_;
v_x_1617_ = v___x_1692_;
v_x_1618_ = v___x_1694_;
goto _start;
}
else
{
lean_dec(v_x_1618_);
if (v_skipConstInApp_1613_ == 0)
{
goto v___jp_1685_;
}
else
{
uint8_t v___x_1696_; 
v___x_1696_ = l_Lean_Expr_isConst(v_x_1616_);
if (v___x_1696_ == 0)
{
goto v___jp_1685_;
}
else
{
v_f_1627_ = v_x_1616_;
v___y_1628_ = v___y_1619_;
v___y_1629_ = v___y_1620_;
v___y_1630_ = v___y_1621_;
v___y_1631_ = v___y_1622_;
v___y_1632_ = v___y_1623_;
v___y_1633_ = v___y_1624_;
goto v___jp_1626_;
}
}
}
v___jp_1626_:
{
if (v_skipInstances_1609_ == 0)
{
size_t v_sz_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
v_sz_1634_ = lean_array_size(v_x_1617_);
v___x_1635_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_1614_);
lean_inc_ref(v_post_1611_);
lean_inc_ref(v_pre_1610_);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1610_, v_post_1611_, v_usedLetOnly_1612_, v_skipConstInApp_1613_, v_skipInstances_1609_, v_postApp_1614_, v_sz_1634_, v___x_1635_, v_x_1617_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v_fst_1638_; lean_object* v_snd_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v_fst_1638_ = lean_ctor_get(v_a_1637_, 0);
lean_inc(v_fst_1638_);
v_snd_1639_ = lean_ctor_get(v_a_1637_, 1);
lean_inc(v_snd_1639_);
lean_dec(v_a_1637_);
v___x_1640_ = l_Lean_mkAppN(v_f_1627_, v_fst_1638_);
lean_dec(v_fst_1638_);
lean_inc_ref(v_postApp_1614_);
lean_inc(v___y_1633_);
lean_inc_ref(v___y_1632_);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
v___x_1641_ = lean_apply_8(v_postApp_1614_, v___y_1615_, v___x_1640_, v_snd_1639_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, lean_box(0));
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v_fst_1643_; lean_object* v_snd_1644_; lean_object* v___x_1645_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v_fst_1643_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_fst_1643_);
v_snd_1644_ = lean_ctor_get(v_a_1642_, 1);
lean_inc(v_snd_1644_);
lean_dec(v_a_1642_);
v___x_1645_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1610_, v_post_1611_, v_usedLetOnly_1612_, v_skipConstInApp_1613_, v_skipInstances_1609_, v_postApp_1614_, v_fst_1643_, v___y_1628_, v_snd_1644_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1645_;
}
else
{
lean_dec_ref(v_postApp_1614_);
lean_dec_ref(v_post_1611_);
lean_dec_ref(v_pre_1610_);
return v___x_1641_;
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v_f_1627_);
lean_dec_ref(v___y_1615_);
lean_dec_ref(v_postApp_1614_);
lean_dec_ref(v_post_1611_);
lean_dec_ref(v_pre_1610_);
v_a_1646_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1636_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1636_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_array_get_size(v_x_1617_);
lean_inc_ref(v_f_1627_);
v___x_1655_ = l_Lean_Meta_getFunInfoNArgs(v_f_1627_, v___x_1654_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v_paramInfo_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v_paramInfo_1657_ = lean_ctor_get(v_a_1656_, 0);
lean_inc_ref(v_paramInfo_1657_);
lean_dec(v_a_1656_);
v___x_1658_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_1614_);
lean_inc_ref(v_post_1611_);
lean_inc_ref(v_pre_1610_);
v___x_1659_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v___x_1654_, v_paramInfo_1657_, v_pre_1610_, v_post_1611_, v_usedLetOnly_1612_, v_skipConstInApp_1613_, v_skipInstances_1609_, v_postApp_1614_, v___x_1658_, v_x_1617_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec_ref(v_paramInfo_1657_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v_fst_1661_; lean_object* v_snd_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v_fst_1661_ = lean_ctor_get(v_a_1660_, 0);
lean_inc(v_fst_1661_);
v_snd_1662_ = lean_ctor_get(v_a_1660_, 1);
lean_inc(v_snd_1662_);
lean_dec(v_a_1660_);
v___x_1663_ = l_Lean_mkAppN(v_f_1627_, v_fst_1661_);
lean_dec(v_fst_1661_);
lean_inc_ref(v_postApp_1614_);
lean_inc(v___y_1633_);
lean_inc_ref(v___y_1632_);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
v___x_1664_ = lean_apply_8(v_postApp_1614_, v___y_1615_, v___x_1663_, v_snd_1662_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, lean_box(0));
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v_fst_1666_; lean_object* v_snd_1667_; lean_object* v___x_1668_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v_fst_1666_ = lean_ctor_get(v_a_1665_, 0);
lean_inc(v_fst_1666_);
v_snd_1667_ = lean_ctor_get(v_a_1665_, 1);
lean_inc(v_snd_1667_);
lean_dec(v_a_1665_);
v___x_1668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1610_, v_post_1611_, v_usedLetOnly_1612_, v_skipConstInApp_1613_, v_skipInstances_1609_, v_postApp_1614_, v_fst_1666_, v___y_1628_, v_snd_1667_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1668_;
}
else
{
lean_dec_ref(v_postApp_1614_);
lean_dec_ref(v_post_1611_);
lean_dec_ref(v_pre_1610_);
return v___x_1664_;
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec_ref(v_f_1627_);
lean_dec_ref(v___y_1615_);
lean_dec_ref(v_postApp_1614_);
lean_dec_ref(v_post_1611_);
lean_dec_ref(v_pre_1610_);
v_a_1669_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1659_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1659_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v___y_1629_);
lean_dec_ref(v_f_1627_);
lean_dec_ref(v_x_1617_);
lean_dec_ref(v___y_1615_);
lean_dec_ref(v_postApp_1614_);
lean_dec_ref(v_post_1611_);
lean_dec_ref(v_pre_1610_);
v_a_1677_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1655_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1655_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
v___jp_1685_:
{
lean_object* v___x_1686_; 
lean_inc_ref(v_postApp_1614_);
lean_inc_ref(v_post_1611_);
lean_inc_ref(v_pre_1610_);
v___x_1686_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1610_, v_post_1611_, v_usedLetOnly_1612_, v_skipConstInApp_1613_, v_skipInstances_1609_, v_postApp_1614_, v_x_1616_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v_fst_1688_; lean_object* v_snd_1689_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v_fst_1688_ = lean_ctor_get(v_a_1687_, 0);
lean_inc(v_fst_1688_);
v_snd_1689_ = lean_ctor_get(v_a_1687_, 1);
lean_inc(v_snd_1689_);
lean_dec(v_a_1687_);
v_f_1627_ = v_fst_1688_;
v___y_1628_ = v___y_1619_;
v___y_1629_ = v_snd_1689_;
v___y_1630_ = v___y_1621_;
v___y_1631_ = v___y_1622_;
v___y_1632_ = v___y_1623_;
v___y_1633_ = v___y_1624_;
goto v___jp_1626_;
}
else
{
lean_dec_ref(v_x_1617_);
lean_dec_ref(v___y_1615_);
lean_dec_ref(v_postApp_1614_);
lean_dec_ref(v_post_1611_);
lean_dec_ref(v_pre_1610_);
return v___x_1686_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1697_, lean_object* v_pre_1698_, lean_object* v_e_1699_, lean_object* v_post_1700_, uint8_t v_usedLetOnly_1701_, uint8_t v_skipConstInApp_1702_, uint8_t v_skipInstances_1703_, lean_object* v_postApp_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_Core_checkSystem(v___x_1697_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v___x_1713_; 
lean_dec_ref_known(v___x_1712_, 1);
lean_inc_ref(v_pre_1698_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
lean_inc(v___y_1708_);
lean_inc_ref(v___y_1707_);
lean_inc_ref(v_e_1699_);
v___x_1713_ = lean_apply_7(v_pre_1698_, v_e_1699_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, lean_box(0));
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1775_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1775_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1775_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v_fst_1718_; lean_object* v_snd_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1774_; 
v_fst_1718_ = lean_ctor_get(v_a_1714_, 0);
v_snd_1719_ = lean_ctor_get(v_a_1714_, 1);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_a_1714_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1721_ = v_a_1714_;
v_isShared_1722_ = v_isSharedCheck_1774_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_snd_1719_);
lean_inc(v_fst_1718_);
lean_dec(v_a_1714_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1774_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___y_1724_; 
switch(lean_obj_tag(v_fst_1718_))
{
case 0:
{
lean_object* v_e_1763_; lean_object* v___x_1765_; 
lean_dec_ref(v_postApp_1704_);
lean_dec_ref(v_post_1700_);
lean_dec_ref(v_e_1699_);
lean_dec_ref(v_pre_1698_);
v_e_1763_ = lean_ctor_get(v_fst_1718_, 0);
lean_inc_ref(v_e_1763_);
lean_dec_ref_known(v_fst_1718_, 1);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v_e_1763_);
v___x_1765_ = v___x_1721_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_e_1763_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_snd_1719_);
v___x_1765_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1767_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1765_);
v___x_1767_ = v___x_1716_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
case 1:
{
lean_object* v_e_1770_; lean_object* v___x_1771_; 
lean_del_object(v___x_1721_);
lean_del_object(v___x_1716_);
lean_dec_ref(v_e_1699_);
v_e_1770_ = lean_ctor_get(v_fst_1718_, 0);
lean_inc_ref(v_e_1770_);
lean_dec_ref_known(v_fst_1718_, 1);
v___x_1771_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v_e_1770_, v___y_1705_, v_snd_1719_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1771_;
}
default: 
{
lean_object* v_e_x3f_1772_; 
lean_del_object(v___x_1721_);
lean_del_object(v___x_1716_);
v_e_x3f_1772_ = lean_ctor_get(v_fst_1718_, 0);
lean_inc(v_e_x3f_1772_);
lean_dec_ref_known(v_fst_1718_, 1);
if (lean_obj_tag(v_e_x3f_1772_) == 0)
{
v___y_1724_ = v_e_1699_;
goto v___jp_1723_;
}
else
{
lean_object* v_val_1773_; 
lean_dec_ref(v_e_1699_);
v_val_1773_ = lean_ctor_get(v_e_x3f_1772_, 0);
lean_inc(v_val_1773_);
lean_dec_ref_known(v_e_x3f_1772_, 1);
v___y_1724_ = v_val_1773_;
goto v___jp_1723_;
}
}
}
v___jp_1723_:
{
switch(lean_obj_tag(v___y_1724_))
{
case 7:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1726_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v___x_1725_, v___y_1724_, v___y_1705_, v_snd_1719_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1726_;
}
case 6:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1728_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v___x_1727_, v___y_1724_, v___y_1705_, v_snd_1719_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1728_;
}
case 8:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1730_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v___x_1729_, v___y_1724_, v___y_1705_, v_snd_1719_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1730_;
}
case 5:
{
lean_object* v_dummy_1731_; lean_object* v_nargs_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_dummy_1731_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1732_ = l_Lean_Expr_getAppNumArgs(v___y_1724_);
lean_inc(v_nargs_1732_);
v___x_1733_ = lean_mk_array(v_nargs_1732_, v_dummy_1731_);
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_sub(v_nargs_1732_, v___x_1734_);
lean_dec(v_nargs_1732_);
lean_inc_ref(v___y_1724_);
v___x_1736_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_skipInstances_1703_, v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_postApp_1704_, v___y_1724_, v___y_1724_, v___x_1733_, v___x_1735_, v___y_1705_, v_snd_1719_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1736_;
}
case 10:
{
lean_object* v_data_1737_; lean_object* v_expr_1738_; lean_object* v___x_1739_; 
v_data_1737_ = lean_ctor_get(v___y_1724_, 0);
v_expr_1738_ = lean_ctor_get(v___y_1724_, 1);
lean_inc_ref(v_expr_1738_);
lean_inc_ref(v_postApp_1704_);
lean_inc_ref(v_post_1700_);
lean_inc_ref(v_pre_1698_);
v___x_1739_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v_expr_1738_, v___y_1705_, v_snd_1719_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v_fst_1741_; lean_object* v_snd_1742_; size_t v___x_1743_; size_t v___x_1744_; uint8_t v___x_1745_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v_fst_1741_ = lean_ctor_get(v_a_1740_, 0);
lean_inc(v_fst_1741_);
v_snd_1742_ = lean_ctor_get(v_a_1740_, 1);
lean_inc(v_snd_1742_);
lean_dec(v_a_1740_);
v___x_1743_ = lean_ptr_addr(v_expr_1738_);
v___x_1744_ = lean_ptr_addr(v_fst_1741_);
v___x_1745_ = lean_usize_dec_eq(v___x_1743_, v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_inc(v_data_1737_);
lean_dec_ref_known(v___y_1724_, 2);
v___x_1746_ = l_Lean_Expr_mdata___override(v_data_1737_, v_fst_1741_);
v___x_1747_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v___x_1746_, v___y_1705_, v_snd_1742_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; 
lean_dec(v_fst_1741_);
v___x_1748_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v___y_1724_, v___y_1705_, v_snd_1742_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1748_;
}
}
else
{
lean_dec_ref_known(v___y_1724_, 2);
lean_dec_ref(v_postApp_1704_);
lean_dec_ref(v_post_1700_);
lean_dec_ref(v_pre_1698_);
return v___x_1739_;
}
}
case 11:
{
lean_object* v_typeName_1749_; lean_object* v_idx_1750_; lean_object* v_struct_1751_; lean_object* v___x_1752_; 
v_typeName_1749_ = lean_ctor_get(v___y_1724_, 0);
v_idx_1750_ = lean_ctor_get(v___y_1724_, 1);
v_struct_1751_ = lean_ctor_get(v___y_1724_, 2);
lean_inc_ref(v_struct_1751_);
lean_inc_ref(v_postApp_1704_);
lean_inc_ref(v_post_1700_);
lean_inc_ref(v_pre_1698_);
v___x_1752_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v_struct_1751_, v___y_1705_, v_snd_1719_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v_fst_1754_; lean_object* v_snd_1755_; size_t v___x_1756_; size_t v___x_1757_; uint8_t v___x_1758_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v_fst_1754_ = lean_ctor_get(v_a_1753_, 0);
lean_inc(v_fst_1754_);
v_snd_1755_ = lean_ctor_get(v_a_1753_, 1);
lean_inc(v_snd_1755_);
lean_dec(v_a_1753_);
v___x_1756_ = lean_ptr_addr(v_struct_1751_);
v___x_1757_ = lean_ptr_addr(v_fst_1754_);
v___x_1758_ = lean_usize_dec_eq(v___x_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_inc(v_idx_1750_);
lean_inc(v_typeName_1749_);
lean_dec_ref_known(v___y_1724_, 3);
v___x_1759_ = l_Lean_Expr_proj___override(v_typeName_1749_, v_idx_1750_, v_fst_1754_);
v___x_1760_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v___x_1759_, v___y_1705_, v_snd_1755_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; 
lean_dec(v_fst_1754_);
v___x_1761_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v___y_1724_, v___y_1705_, v_snd_1755_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1761_;
}
}
else
{
lean_dec_ref_known(v___y_1724_, 3);
lean_dec_ref(v_postApp_1704_);
lean_dec_ref(v_post_1700_);
lean_dec_ref(v_pre_1698_);
return v___x_1752_;
}
}
default: 
{
lean_object* v___x_1762_; 
v___x_1762_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1698_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_postApp_1704_, v___y_1724_, v___y_1705_, v_snd_1719_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1762_;
}
}
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref(v_postApp_1704_);
lean_dec_ref(v_post_1700_);
lean_dec_ref(v_e_1699_);
lean_dec_ref(v_pre_1698_);
v_a_1776_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1713_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1713_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
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
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec(v___y_1706_);
lean_dec_ref(v_postApp_1704_);
lean_dec_ref(v_post_1700_);
lean_dec_ref(v_e_1699_);
lean_dec_ref(v_pre_1698_);
v_a_1784_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1712_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1712_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1792_, lean_object* v_pre_1793_, lean_object* v_e_1794_, lean_object* v_post_1795_, lean_object* v_usedLetOnly_1796_, lean_object* v_skipConstInApp_1797_, lean_object* v_skipInstances_1798_, lean_object* v_postApp_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
uint8_t v_usedLetOnly_boxed_1807_; uint8_t v_skipConstInApp_boxed_1808_; uint8_t v_skipInstances_boxed_1809_; lean_object* v_res_1810_; 
v_usedLetOnly_boxed_1807_ = lean_unbox(v_usedLetOnly_1796_);
v_skipConstInApp_boxed_1808_ = lean_unbox(v_skipConstInApp_1797_);
v_skipInstances_boxed_1809_ = lean_unbox(v_skipInstances_1798_);
v_res_1810_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1792_, v_pre_1793_, v_e_1794_, v_post_1795_, v_usedLetOnly_boxed_1807_, v_skipConstInApp_boxed_1808_, v_skipInstances_boxed_1809_, v_postApp_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1800_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1811_, lean_object* v_post_1812_, uint8_t v_usedLetOnly_1813_, uint8_t v_skipConstInApp_1814_, uint8_t v_skipInstances_1815_, lean_object* v_postApp_1816_, lean_object* v_e_1817_, lean_object* v_a_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_inc(v_a_1818_);
v___x_1825_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1825_, 0, lean_box(0));
lean_closure_set(v___x_1825_, 1, lean_box(0));
lean_closure_set(v___x_1825_, 2, v_a_1818_);
v___x_1826_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1825_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1881_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1881_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1881_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_fst_1831_; lean_object* v_snd_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1880_; 
v_fst_1831_ = lean_ctor_get(v_a_1827_, 0);
v_snd_1832_ = lean_ctor_get(v_a_1827_, 1);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_a_1827_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1834_ = v_a_1827_;
v_isShared_1835_ = v_isSharedCheck_1880_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_snd_1832_);
lean_inc(v_fst_1831_);
lean_dec(v_a_1827_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1880_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___redArg(v_fst_1831_, v_e_1817_);
lean_dec(v_fst_1831_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; 
lean_del_object(v___x_1834_);
lean_del_object(v___x_1829_);
v___x_1837_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1838_ = lean_box(v_usedLetOnly_1813_);
v___x_1839_ = lean_box(v_skipConstInApp_1814_);
v___x_1840_ = lean_box(v_skipInstances_1815_);
lean_inc_ref(v_e_1817_);
v___f_1841_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1841_, 0, v___x_1837_);
lean_closure_set(v___f_1841_, 1, v_pre_1811_);
lean_closure_set(v___f_1841_, 2, v_e_1817_);
lean_closure_set(v___f_1841_, 3, v_post_1812_);
lean_closure_set(v___f_1841_, 4, v___x_1838_);
lean_closure_set(v___f_1841_, 5, v___x_1839_);
lean_closure_set(v___f_1841_, 6, v___x_1840_);
lean_closure_set(v___f_1841_, 7, v_postApp_1816_);
v___x_1842_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___f_1841_, v_a_1818_, v_snd_1832_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v_fst_1844_; lean_object* v_snd_1845_; lean_object* v___f_1846_; lean_object* v___x_1847_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v_fst_1844_ = lean_ctor_get(v_a_1843_, 0);
lean_inc_n(v_fst_1844_, 2);
v_snd_1845_ = lean_ctor_get(v_a_1843_, 1);
lean_inc(v_snd_1845_);
lean_dec(v_a_1843_);
lean_inc(v_a_1818_);
v___f_1846_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1846_, 0, v_a_1818_);
lean_closure_set(v___f_1846_, 1, v_e_1817_);
lean_closure_set(v___f_1846_, 2, v_fst_1844_);
v___x_1847_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1846_, v_snd_1845_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1864_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1864_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1864_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v_snd_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1862_; 
v_snd_1852_ = lean_ctor_get(v_a_1848_, 1);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_a_1848_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v_a_1848_, 0);
lean_dec(v_unused_1863_);
v___x_1854_ = v_a_1848_;
v_isShared_1855_ = v_isSharedCheck_1862_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_snd_1852_);
lean_dec(v_a_1848_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1862_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_fst_1844_);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_fst_1844_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_snd_1852_);
v___x_1857_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1859_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1857_);
v___x_1859_ = v___x_1850_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_fst_1844_);
v_a_1865_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1847_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1847_);
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
lean_dec_ref(v_e_1817_);
return v___x_1842_;
}
}
else
{
lean_object* v_val_1873_; lean_object* v___x_1875_; 
lean_dec_ref(v_e_1817_);
lean_dec_ref(v_postApp_1816_);
lean_dec_ref(v_post_1812_);
lean_dec_ref(v_pre_1811_);
v_val_1873_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_val_1873_);
lean_dec_ref_known(v___x_1836_, 1);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v_val_1873_);
v___x_1875_ = v___x_1834_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_val_1873_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_snd_1832_);
v___x_1875_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1875_);
v___x_1877_ = v___x_1829_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v_e_1817_);
lean_dec_ref(v_postApp_1816_);
lean_dec_ref(v_post_1812_);
lean_dec_ref(v_pre_1811_);
v_a_1882_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1826_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1826_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1890_, lean_object* v_post_1891_, uint8_t v_usedLetOnly_1892_, uint8_t v_skipConstInApp_1893_, uint8_t v_skipInstances_1894_, lean_object* v_postApp_1895_, lean_object* v_fvars_1896_, lean_object* v_e_1897_, lean_object* v_a_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
if (lean_obj_tag(v_e_1897_) == 7)
{
lean_object* v_binderName_1905_; lean_object* v_binderType_1906_; lean_object* v_body_1907_; uint8_t v_binderInfo_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_binderName_1905_ = lean_ctor_get(v_e_1897_, 0);
lean_inc(v_binderName_1905_);
v_binderType_1906_ = lean_ctor_get(v_e_1897_, 1);
lean_inc_ref(v_binderType_1906_);
v_body_1907_ = lean_ctor_get(v_e_1897_, 2);
lean_inc_ref(v_body_1907_);
v_binderInfo_1908_ = lean_ctor_get_uint8(v_e_1897_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1897_, 3);
v___x_1909_ = lean_box(v_usedLetOnly_1892_);
v___x_1910_ = lean_box(v_skipConstInApp_1893_);
v___x_1911_ = lean_box(v_skipInstances_1894_);
lean_inc_ref(v_postApp_1895_);
lean_inc_ref(v_post_1891_);
lean_inc_ref(v_pre_1890_);
lean_inc_ref(v_fvars_1896_);
v___f_1912_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 16, 8);
lean_closure_set(v___f_1912_, 0, v_fvars_1896_);
lean_closure_set(v___f_1912_, 1, v_pre_1890_);
lean_closure_set(v___f_1912_, 2, v_post_1891_);
lean_closure_set(v___f_1912_, 3, v___x_1909_);
lean_closure_set(v___f_1912_, 4, v___x_1910_);
lean_closure_set(v___f_1912_, 5, v___x_1911_);
lean_closure_set(v___f_1912_, 6, v_postApp_1895_);
lean_closure_set(v___f_1912_, 7, v_body_1907_);
v___x_1913_ = lean_expr_instantiate_rev(v_binderType_1906_, v_fvars_1896_);
lean_dec_ref(v_fvars_1896_);
lean_dec_ref(v_binderType_1906_);
v___x_1914_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1890_, v_post_1891_, v_usedLetOnly_1892_, v_skipConstInApp_1893_, v_skipInstances_1894_, v_postApp_1895_, v___x_1913_, v_a_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v_fst_1916_; lean_object* v_snd_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
v_fst_1916_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_fst_1916_);
v_snd_1917_ = lean_ctor_get(v_a_1915_, 1);
lean_inc(v_snd_1917_);
lean_dec(v_a_1915_);
v___x_1918_ = 0;
v___x_1919_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_binderName_1905_, v_binderInfo_1908_, v_fst_1916_, v___f_1912_, v___x_1918_, v_a_1898_, v_snd_1917_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
return v___x_1919_;
}
else
{
lean_dec_ref(v___f_1912_);
lean_dec(v_binderName_1905_);
return v___x_1914_;
}
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_expr_instantiate_rev(v_e_1897_, v_fvars_1896_);
lean_dec_ref(v_e_1897_);
lean_inc_ref(v_postApp_1895_);
lean_inc_ref(v_post_1891_);
lean_inc_ref(v_pre_1890_);
v___x_1921_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1890_, v_post_1891_, v_usedLetOnly_1892_, v_skipConstInApp_1893_, v_skipInstances_1894_, v_postApp_1895_, v___x_1920_, v_a_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v_fst_1923_; lean_object* v_snd_1924_; uint8_t v___x_1925_; uint8_t v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v_fst_1923_ = lean_ctor_get(v_a_1922_, 0);
lean_inc(v_fst_1923_);
v_snd_1924_ = lean_ctor_get(v_a_1922_, 1);
lean_inc(v_snd_1924_);
lean_dec(v_a_1922_);
v___x_1925_ = 0;
v___x_1926_ = 1;
v___x_1927_ = 1;
v___x_1928_ = l_Lean_Meta_mkForallFVars(v_fvars_1896_, v_fst_1923_, v___x_1925_, v_usedLetOnly_1892_, v___x_1926_, v___x_1927_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec_ref(v_fvars_1896_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1890_, v_post_1891_, v_usedLetOnly_1892_, v_skipConstInApp_1893_, v_skipInstances_1894_, v_postApp_1895_, v_a_1929_, v_a_1898_, v_snd_1924_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
return v___x_1930_;
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_snd_1924_);
lean_dec_ref(v_postApp_1895_);
lean_dec_ref(v_post_1891_);
lean_dec_ref(v_pre_1890_);
v_a_1931_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1928_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1928_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1896_);
lean_dec_ref(v_postApp_1895_);
lean_dec_ref(v_post_1891_);
lean_dec_ref(v_pre_1890_);
return v___x_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1939_, lean_object* v_pre_1940_, lean_object* v_post_1941_, uint8_t v_usedLetOnly_1942_, uint8_t v_skipConstInApp_1943_, uint8_t v_skipInstances_1944_, lean_object* v_postApp_1945_, lean_object* v_body_1946_, lean_object* v_x_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_array_push(v_fvars_1939_, v_x_1947_);
v___x_1956_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1940_, v_post_1941_, v_usedLetOnly_1942_, v_skipConstInApp_1943_, v_skipInstances_1944_, v_postApp_1945_, v___x_1955_, v_body_1946_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object* v_pre_1957_, lean_object* v_post_1958_, lean_object* v_usedLetOnly_1959_, lean_object* v_skipConstInApp_1960_, lean_object* v_skipInstances_1961_, lean_object* v_postApp_1962_, lean_object* v_sz_1963_, lean_object* v_i_1964_, lean_object* v_bs_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
uint8_t v_usedLetOnly_boxed_1973_; uint8_t v_skipConstInApp_boxed_1974_; uint8_t v_skipInstances_boxed_1975_; size_t v_sz_boxed_1976_; size_t v_i_boxed_1977_; lean_object* v_res_1978_; 
v_usedLetOnly_boxed_1973_ = lean_unbox(v_usedLetOnly_1959_);
v_skipConstInApp_boxed_1974_ = lean_unbox(v_skipConstInApp_1960_);
v_skipInstances_boxed_1975_ = lean_unbox(v_skipInstances_1961_);
v_sz_boxed_1976_ = lean_unbox_usize(v_sz_1963_);
lean_dec(v_sz_1963_);
v_i_boxed_1977_ = lean_unbox_usize(v_i_1964_);
lean_dec(v_i_1964_);
v_res_1978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1957_, v_post_1958_, v_usedLetOnly_boxed_1973_, v_skipConstInApp_boxed_1974_, v_skipInstances_boxed_1975_, v_postApp_1962_, v_sz_boxed_1976_, v_i_boxed_1977_, v_bs_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1966_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_pre_1979_, lean_object* v_post_1980_, lean_object* v_usedLetOnly_1981_, lean_object* v_skipConstInApp_1982_, lean_object* v_skipInstances_1983_, lean_object* v_postApp_1984_, lean_object* v_e_1985_, lean_object* v_a_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
uint8_t v_usedLetOnly_boxed_1993_; uint8_t v_skipConstInApp_boxed_1994_; uint8_t v_skipInstances_boxed_1995_; lean_object* v_res_1996_; 
v_usedLetOnly_boxed_1993_ = lean_unbox(v_usedLetOnly_1981_);
v_skipConstInApp_boxed_1994_ = lean_unbox(v_skipConstInApp_1982_);
v_skipInstances_boxed_1995_ = lean_unbox(v_skipInstances_1983_);
v_res_1996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_pre_1979_, v_post_1980_, v_usedLetOnly_boxed_1993_, v_skipConstInApp_boxed_1994_, v_skipInstances_boxed_1995_, v_postApp_1984_, v_e_1985_, v_a_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v_a_1986_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1997_, lean_object* v_post_1998_, lean_object* v_usedLetOnly_1999_, lean_object* v_skipConstInApp_2000_, lean_object* v_skipInstances_2001_, lean_object* v_postApp_2002_, lean_object* v_fvars_2003_, lean_object* v_e_2004_, lean_object* v_a_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v_usedLetOnly_boxed_2012_; uint8_t v_skipConstInApp_boxed_2013_; uint8_t v_skipInstances_boxed_2014_; lean_object* v_res_2015_; 
v_usedLetOnly_boxed_2012_ = lean_unbox(v_usedLetOnly_1999_);
v_skipConstInApp_boxed_2013_ = lean_unbox(v_skipConstInApp_2000_);
v_skipInstances_boxed_2014_ = lean_unbox(v_skipInstances_2001_);
v_res_2015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1997_, v_post_1998_, v_usedLetOnly_boxed_2012_, v_skipConstInApp_boxed_2013_, v_skipInstances_boxed_2014_, v_postApp_2002_, v_fvars_2003_, v_e_2004_, v_a_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v_a_2005_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_2016_, lean_object* v_post_2017_, lean_object* v_usedLetOnly_2018_, lean_object* v_skipConstInApp_2019_, lean_object* v_skipInstances_2020_, lean_object* v_postApp_2021_, lean_object* v_fvars_2022_, lean_object* v_e_2023_, lean_object* v_a_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
uint8_t v_usedLetOnly_boxed_2031_; uint8_t v_skipConstInApp_boxed_2032_; uint8_t v_skipInstances_boxed_2033_; lean_object* v_res_2034_; 
v_usedLetOnly_boxed_2031_ = lean_unbox(v_usedLetOnly_2018_);
v_skipConstInApp_boxed_2032_ = lean_unbox(v_skipConstInApp_2019_);
v_skipInstances_boxed_2033_ = lean_unbox(v_skipInstances_2020_);
v_res_2034_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_2016_, v_post_2017_, v_usedLetOnly_boxed_2031_, v_skipConstInApp_boxed_2032_, v_skipInstances_boxed_2033_, v_postApp_2021_, v_fvars_2022_, v_e_2023_, v_a_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v_a_2024_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_2035_, lean_object* v_post_2036_, lean_object* v_usedLetOnly_2037_, lean_object* v_skipConstInApp_2038_, lean_object* v_skipInstances_2039_, lean_object* v_postApp_2040_, lean_object* v_e_2041_, lean_object* v_a_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v_usedLetOnly_boxed_2049_; uint8_t v_skipConstInApp_boxed_2050_; uint8_t v_skipInstances_boxed_2051_; lean_object* v_res_2052_; 
v_usedLetOnly_boxed_2049_ = lean_unbox(v_usedLetOnly_2037_);
v_skipConstInApp_boxed_2050_ = lean_unbox(v_skipConstInApp_2038_);
v_skipInstances_boxed_2051_ = lean_unbox(v_skipInstances_2039_);
v_res_2052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2035_, v_post_2036_, v_usedLetOnly_boxed_2049_, v_skipConstInApp_boxed_2050_, v_skipInstances_boxed_2051_, v_postApp_2040_, v_e_2041_, v_a_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v_a_2042_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_pre_2053_, lean_object* v_post_2054_, lean_object* v_usedLetOnly_2055_, lean_object* v_skipConstInApp_2056_, lean_object* v_skipInstances_2057_, lean_object* v_postApp_2058_, lean_object* v_fvars_2059_, lean_object* v_e_2060_, lean_object* v_a_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
uint8_t v_usedLetOnly_boxed_2068_; uint8_t v_skipConstInApp_boxed_2069_; uint8_t v_skipInstances_boxed_2070_; lean_object* v_res_2071_; 
v_usedLetOnly_boxed_2068_ = lean_unbox(v_usedLetOnly_2055_);
v_skipConstInApp_boxed_2069_ = lean_unbox(v_skipConstInApp_2056_);
v_skipInstances_boxed_2070_ = lean_unbox(v_skipInstances_2057_);
v_res_2071_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_2053_, v_post_2054_, v_usedLetOnly_boxed_2068_, v_skipConstInApp_boxed_2069_, v_skipInstances_boxed_2070_, v_postApp_2058_, v_fvars_2059_, v_e_2060_, v_a_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v_a_2061_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_2072_ = _args[0];
lean_object* v___x_2073_ = _args[1];
lean_object* v_pre_2074_ = _args[2];
lean_object* v_post_2075_ = _args[3];
lean_object* v_usedLetOnly_2076_ = _args[4];
lean_object* v_skipConstInApp_2077_ = _args[5];
lean_object* v_skipInstances_2078_ = _args[6];
lean_object* v_postApp_2079_ = _args[7];
lean_object* v_a_2080_ = _args[8];
lean_object* v_b_2081_ = _args[9];
lean_object* v___y_2082_ = _args[10];
lean_object* v___y_2083_ = _args[11];
lean_object* v___y_2084_ = _args[12];
lean_object* v___y_2085_ = _args[13];
lean_object* v___y_2086_ = _args[14];
lean_object* v___y_2087_ = _args[15];
lean_object* v___y_2088_ = _args[16];
_start:
{
uint8_t v_usedLetOnly_boxed_2089_; uint8_t v_skipConstInApp_boxed_2090_; uint8_t v_skipInstances_boxed_2091_; lean_object* v_res_2092_; 
v_usedLetOnly_boxed_2089_ = lean_unbox(v_usedLetOnly_2076_);
v_skipConstInApp_boxed_2090_ = lean_unbox(v_skipConstInApp_2077_);
v_skipInstances_boxed_2091_ = lean_unbox(v_skipInstances_2078_);
v_res_2092_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_upperBound_2072_, v___x_2073_, v_pre_2074_, v_post_2075_, v_usedLetOnly_boxed_2089_, v_skipConstInApp_boxed_2090_, v_skipInstances_boxed_2091_, v_postApp_2079_, v_a_2080_, v_b_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2082_);
lean_dec_ref(v___x_2073_);
lean_dec(v_upperBound_2072_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object** _args){
lean_object* v_skipInstances_2093_ = _args[0];
lean_object* v_pre_2094_ = _args[1];
lean_object* v_post_2095_ = _args[2];
lean_object* v_usedLetOnly_2096_ = _args[3];
lean_object* v_skipConstInApp_2097_ = _args[4];
lean_object* v_postApp_2098_ = _args[5];
lean_object* v___y_2099_ = _args[6];
lean_object* v_x_2100_ = _args[7];
lean_object* v_x_2101_ = _args[8];
lean_object* v_x_2102_ = _args[9];
lean_object* v___y_2103_ = _args[10];
lean_object* v___y_2104_ = _args[11];
lean_object* v___y_2105_ = _args[12];
lean_object* v___y_2106_ = _args[13];
lean_object* v___y_2107_ = _args[14];
lean_object* v___y_2108_ = _args[15];
lean_object* v___y_2109_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2110_; uint8_t v_usedLetOnly_boxed_2111_; uint8_t v_skipConstInApp_boxed_2112_; lean_object* v_res_2113_; 
v_skipInstances_boxed_2110_ = lean_unbox(v_skipInstances_2093_);
v_usedLetOnly_boxed_2111_ = lean_unbox(v_usedLetOnly_2096_);
v_skipConstInApp_boxed_2112_ = lean_unbox(v_skipConstInApp_2097_);
v_res_2113_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_skipInstances_boxed_2110_, v_pre_2094_, v_post_2095_, v_usedLetOnly_boxed_2111_, v_skipConstInApp_boxed_2112_, v_postApp_2098_, v___y_2099_, v_x_2100_, v_x_2101_, v_x_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2103_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2114_, lean_object* v_x_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = lean_apply_1(v_x_2115_, lean_box(0));
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___y_2116_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2125_, lean_object* v_x_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2125_, v_x_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__1(lean_object* v_x_2134_, lean_object* v_e_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v_e_2135_);
lean_ctor_set(v___x_2142_, 1, v___y_2136_);
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__1___boxed(lean_object* v_x_2144_, lean_object* v_e_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__1(v_x_2144_, v_e_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v_x_2144_);
return v_res_2152_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = lean_box(0);
v___x_2155_ = lean_unsigned_to_nat(16u);
v___x_2156_ = lean_mk_array(v___x_2155_, v___x_2154_);
return v___x_2156_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2158_ = lean_unsigned_to_nat(0u);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
lean_ctor_set(v___x_2159_, 1, v___x_2157_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2161_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2161_, 0, lean_box(0));
lean_closure_set(v___x_2161_, 1, lean_box(0));
lean_closure_set(v___x_2161_, 2, v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2162_, lean_object* v_pre_2163_, lean_object* v_post_2164_, uint8_t v_usedLetOnly_2165_, uint8_t v_skipConstInApp_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___f_2173_; uint8_t v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v_a_2177_; lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v___x_2180_; 
v___f_2173_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0));
v___x_2174_ = 0;
v___x_2175_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3);
v___x_2176_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2175_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref(v___x_2176_);
v_fst_2178_ = lean_ctor_get(v_a_2177_, 0);
lean_inc(v_fst_2178_);
v_snd_2179_ = lean_ctor_get(v_a_2177_, 1);
lean_inc(v_snd_2179_);
lean_dec(v_a_2177_);
v___x_2180_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2163_, v_post_2164_, v_usedLetOnly_2165_, v_skipConstInApp_2166_, v___x_2174_, v___f_2173_, v_input_2162_, v_fst_2178_, v_snd_2179_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v_fst_2182_; lean_object* v_snd_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2202_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v_fst_2182_ = lean_ctor_get(v_a_2181_, 0);
lean_inc(v_fst_2182_);
v_snd_2183_ = lean_ctor_get(v_a_2181_, 1);
lean_inc(v_snd_2183_);
lean_dec(v_a_2181_);
v___x_2184_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2184_, 0, lean_box(0));
lean_closure_set(v___x_2184_, 1, lean_box(0));
lean_closure_set(v___x_2184_, 2, v_fst_2178_);
v___x_2185_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2184_, v_snd_2183_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2202_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2202_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_snd_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2200_; 
v_snd_2190_ = lean_ctor_get(v_a_2186_, 1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_a_2186_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; 
v_unused_2201_ = lean_ctor_get(v_a_2186_, 0);
lean_dec(v_unused_2201_);
v___x_2192_ = v_a_2186_;
v_isShared_2193_ = v_isSharedCheck_2200_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_snd_2190_);
lean_dec(v_a_2186_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2200_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_fst_2182_);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_fst_2182_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_snd_2190_);
v___x_2195_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2197_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2195_);
v___x_2197_ = v___x_2188_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
lean_dec(v_fst_2178_);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2203_, lean_object* v_pre_2204_, lean_object* v_post_2205_, lean_object* v_usedLetOnly_2206_, lean_object* v_skipConstInApp_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
uint8_t v_usedLetOnly_boxed_2214_; uint8_t v_skipConstInApp_boxed_2215_; lean_object* v_res_2216_; 
v_usedLetOnly_boxed_2214_ = lean_unbox(v_usedLetOnly_2206_);
v_skipConstInApp_boxed_2215_ = lean_unbox(v_skipConstInApp_2207_);
v_res_2216_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2203_, v_pre_2204_, v_post_2205_, v_usedLetOnly_boxed_2214_, v_skipConstInApp_boxed_2215_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v___y_2226_; lean_object* v___x_2243_; uint8_t v_transparency_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; uint8_t v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2243_ = l_Lean_Meta_Context_config(v_a_2220_);
v_transparency_2244_ = lean_ctor_get_uint8(v___x_2243_, 9);
lean_dec_ref(v___x_2243_);
v___f_2245_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2246_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2247_ = 0;
v___x_2248_ = 3;
v___x_2249_ = lean_box(0);
v___x_2250_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2244_, v___x_2248_);
if (v___x_2250_ == 0)
{
lean_object* v_keyedConfig_2251_; uint8_t v_trackZetaDelta_2252_; lean_object* v_zetaDeltaSet_2253_; lean_object* v_lctx_2254_; lean_object* v_localInstances_2255_; lean_object* v_defEqCtx_x3f_2256_; lean_object* v_synthPendingDepth_2257_; lean_object* v_customCanUnfoldPredicate_x3f_2258_; uint8_t v_univApprox_2259_; uint8_t v_inTypeClassResolution_2260_; uint8_t v_cacheInferType_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_keyedConfig_2251_ = lean_ctor_get(v_a_2220_, 0);
v_trackZetaDelta_2252_ = lean_ctor_get_uint8(v_a_2220_, sizeof(void*)*7);
v_zetaDeltaSet_2253_ = lean_ctor_get(v_a_2220_, 1);
v_lctx_2254_ = lean_ctor_get(v_a_2220_, 2);
v_localInstances_2255_ = lean_ctor_get(v_a_2220_, 3);
v_defEqCtx_x3f_2256_ = lean_ctor_get(v_a_2220_, 4);
v_synthPendingDepth_2257_ = lean_ctor_get(v_a_2220_, 5);
v_customCanUnfoldPredicate_x3f_2258_ = lean_ctor_get(v_a_2220_, 6);
v_univApprox_2259_ = lean_ctor_get_uint8(v_a_2220_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2260_ = lean_ctor_get_uint8(v_a_2220_, sizeof(void*)*7 + 2);
v_cacheInferType_2261_ = lean_ctor_get_uint8(v_a_2220_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2251_);
v___x_2262_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2248_, v_keyedConfig_2251_);
lean_inc(v_customCanUnfoldPredicate_x3f_2258_);
lean_inc(v_synthPendingDepth_2257_);
lean_inc(v_defEqCtx_x3f_2256_);
lean_inc_ref(v_localInstances_2255_);
lean_inc_ref(v_lctx_2254_);
lean_inc(v_zetaDeltaSet_2253_);
v___x_2263_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v_zetaDeltaSet_2253_);
lean_ctor_set(v___x_2263_, 2, v_lctx_2254_);
lean_ctor_set(v___x_2263_, 3, v_localInstances_2255_);
lean_ctor_set(v___x_2263_, 4, v_defEqCtx_x3f_2256_);
lean_ctor_set(v___x_2263_, 5, v_synthPendingDepth_2257_);
lean_ctor_set(v___x_2263_, 6, v_customCanUnfoldPredicate_x3f_2258_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*7, v_trackZetaDelta_2252_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*7 + 1, v_univApprox_2259_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2260_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*7 + 3, v_cacheInferType_2261_);
v___x_2264_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2219_, v___f_2246_, v___f_2245_, v___x_2247_, v___x_2247_, v___x_2249_, v___x_2263_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec_ref_known(v___x_2263_, 7);
v___y_2226_ = v___x_2264_;
goto v___jp_2225_;
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2219_, v___f_2246_, v___f_2245_, v___x_2247_, v___x_2247_, v___x_2249_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
v___y_2226_ = v___x_2265_;
goto v___jp_2225_;
}
v___jp_2225_:
{
if (lean_obj_tag(v___y_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_a_2227_ = lean_ctor_get(v___y_2226_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___y_2226_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___y_2226_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___y_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_a_2235_ = lean_ctor_get(v___y_2226_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___y_2226_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___y_2226_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___y_2226_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Meta_expandCoe(v_e_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2273_, lean_object* v_m_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2274_, v_a_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2277_, lean_object* v_m_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2277_, v_m_2278_, v_a_2279_);
lean_dec(v_a_2279_);
lean_dec_ref(v_m_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_){
_start:
{
uint8_t v___x_2284_; 
v___x_2284_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2282_, v_x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_){
_start:
{
uint8_t v_res_2288_; lean_object* v_r_2289_; 
v_res_2288_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2285_, v_x_2286_, v_x_2287_);
lean_dec_ref(v_x_2287_);
lean_dec_ref(v_x_2286_);
v_r_2289_ = lean_box(v_res_2288_);
return v_r_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v___dummy_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg();
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2298_, lean_object* v_a_2299_, lean_object* v_x_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(v_a_2299_, v_x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2302_, lean_object* v_a_2303_, lean_object* v_x_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6(v_00_u03b2_2302_, v_a_2303_, v_x_2304_);
lean_dec(v_x_2304_);
lean_dec(v_a_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_2306_, lean_object* v_m_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___redArg(v_m_2307_, v_a_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2310_, lean_object* v_m_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_00_u03b2_2310_, v_m_2311_, v_a_2312_);
lean_dec_ref(v_a_2312_);
lean_dec_ref(v_m_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_upperBound_2314_, lean_object* v___x_2315_, lean_object* v_pre_2316_, lean_object* v_post_2317_, uint8_t v_usedLetOnly_2318_, uint8_t v_skipConstInApp_2319_, uint8_t v_skipInstances_2320_, lean_object* v_postApp_2321_, lean_object* v___x_2322_, lean_object* v_inst_2323_, lean_object* v_R_2324_, lean_object* v_a_2325_, lean_object* v_b_2326_, lean_object* v_c_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_upperBound_2314_, v___x_2315_, v_pre_2316_, v_post_2317_, v_usedLetOnly_2318_, v_skipConstInApp_2319_, v_skipInstances_2320_, v_postApp_2321_, v_a_2325_, v_b_2326_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_2336_ = _args[0];
lean_object* v___x_2337_ = _args[1];
lean_object* v_pre_2338_ = _args[2];
lean_object* v_post_2339_ = _args[3];
lean_object* v_usedLetOnly_2340_ = _args[4];
lean_object* v_skipConstInApp_2341_ = _args[5];
lean_object* v_skipInstances_2342_ = _args[6];
lean_object* v_postApp_2343_ = _args[7];
lean_object* v___x_2344_ = _args[8];
lean_object* v_inst_2345_ = _args[9];
lean_object* v_R_2346_ = _args[10];
lean_object* v_a_2347_ = _args[11];
lean_object* v_b_2348_ = _args[12];
lean_object* v_c_2349_ = _args[13];
lean_object* v___y_2350_ = _args[14];
lean_object* v___y_2351_ = _args[15];
lean_object* v___y_2352_ = _args[16];
lean_object* v___y_2353_ = _args[17];
lean_object* v___y_2354_ = _args[18];
lean_object* v___y_2355_ = _args[19];
lean_object* v___y_2356_ = _args[20];
_start:
{
uint8_t v_usedLetOnly_boxed_2357_; uint8_t v_skipConstInApp_boxed_2358_; uint8_t v_skipInstances_boxed_2359_; lean_object* v_res_2360_; 
v_usedLetOnly_boxed_2357_ = lean_unbox(v_usedLetOnly_2340_);
v_skipConstInApp_boxed_2358_ = lean_unbox(v_skipConstInApp_2341_);
v_skipInstances_boxed_2359_ = lean_unbox(v_skipInstances_2342_);
v_res_2360_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_upperBound_2336_, v___x_2337_, v_pre_2338_, v_post_2339_, v_usedLetOnly_boxed_2357_, v_skipConstInApp_boxed_2358_, v_skipInstances_boxed_2359_, v_postApp_2343_, v___x_2344_, v_inst_2345_, v_R_2346_, v_a_2347_, v_b_2348_, v_c_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2350_);
lean_dec(v___x_2344_);
lean_dec_ref(v___x_2337_);
lean_dec(v_upperBound_2336_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18(lean_object* v_00_u03b1_2361_, lean_object* v_name_2362_, uint8_t v_bi_2363_, lean_object* v_type_2364_, lean_object* v_k_2365_, uint8_t v_kind_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_name_2362_, v_bi_2363_, v_type_2364_, v_k_2365_, v_kind_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___boxed(lean_object* v_00_u03b1_2375_, lean_object* v_name_2376_, lean_object* v_bi_2377_, lean_object* v_type_2378_, lean_object* v_k_2379_, lean_object* v_kind_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
uint8_t v_bi_boxed_2388_; uint8_t v_kind_boxed_2389_; lean_object* v_res_2390_; 
v_bi_boxed_2388_ = lean_unbox(v_bi_2377_);
v_kind_boxed_2389_ = lean_unbox(v_kind_2380_);
v_res_2390_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18(v_00_u03b1_2375_, v_name_2376_, v_bi_boxed_2388_, v_type_2378_, v_k_2379_, v_kind_boxed_2389_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2381_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21(lean_object* v_00_u03b1_2391_, lean_object* v_name_2392_, lean_object* v_type_2393_, lean_object* v_val_2394_, lean_object* v_k_2395_, uint8_t v_nondep_2396_, uint8_t v_kind_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(v_name_2392_, v_type_2393_, v_val_2394_, v_k_2395_, v_nondep_2396_, v_kind_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___boxed(lean_object* v_00_u03b1_2406_, lean_object* v_name_2407_, lean_object* v_type_2408_, lean_object* v_val_2409_, lean_object* v_k_2410_, lean_object* v_nondep_2411_, lean_object* v_kind_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
uint8_t v_nondep_boxed_2420_; uint8_t v_kind_boxed_2421_; lean_object* v_res_2422_; 
v_nondep_boxed_2420_ = lean_unbox(v_nondep_2411_);
v_kind_boxed_2421_ = lean_unbox(v_kind_2412_);
v_res_2422_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21(v_00_u03b1_2406_, v_name_2407_, v_type_2408_, v_val_2409_, v_k_2410_, v_nondep_boxed_2420_, v_kind_boxed_2421_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2413_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b1_2423_, lean_object* v_ref_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_ref_2424_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b1_2431_, lean_object* v_ref_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b1_2431_, v_ref_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b1_2439_, lean_object* v_x_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_x_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___boxed(lean_object* v_00_u03b1_2449_, lean_object* v_x_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(v_00_u03b1_2449_, v_x_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2451_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18(lean_object* v_00_u03b2_2459_, lean_object* v_m_2460_, lean_object* v_a_2461_, lean_object* v_b_2462_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v_m_2460_, v_a_2461_, v_b_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2464_, lean_object* v_x_2465_, size_t v_x_2466_, lean_object* v_x_2467_){
_start:
{
uint8_t v___x_2468_; 
v___x_2468_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2465_, v_x_2466_, v_x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2469_, lean_object* v_x_2470_, lean_object* v_x_2471_, lean_object* v_x_2472_){
_start:
{
size_t v_x_41725__boxed_2473_; uint8_t v_res_2474_; lean_object* v_r_2475_; 
v_x_41725__boxed_2473_ = lean_unbox_usize(v_x_2471_);
lean_dec(v_x_2471_);
v_res_2474_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2469_, v_x_2470_, v_x_41725__boxed_2473_, v_x_2472_);
lean_dec_ref(v_x_2472_);
lean_dec_ref(v_x_2470_);
v_r_2475_ = lean_box(v_res_2474_);
return v_r_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_2476_, lean_object* v_a_2477_, lean_object* v_x_2478_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13___redArg(v_a_2477_, v_x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2480_, lean_object* v_a_2481_, lean_object* v_x_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_spec__13(v_00_u03b2_2480_, v_a_2481_, v_x_2482_);
lean_dec(v_x_2482_);
lean_dec_ref(v_a_2481_);
return v_res_2483_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26(lean_object* v_00_u03b2_2484_, lean_object* v_a_2485_, lean_object* v_x_2486_){
_start:
{
uint8_t v___x_2487_; 
v___x_2487_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(v_a_2485_, v_x_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___boxed(lean_object* v_00_u03b2_2488_, lean_object* v_a_2489_, lean_object* v_x_2490_){
_start:
{
uint8_t v_res_2491_; lean_object* v_r_2492_; 
v_res_2491_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26(v_00_u03b2_2488_, v_a_2489_, v_x_2490_);
lean_dec(v_x_2490_);
lean_dec_ref(v_a_2489_);
v_r_2492_ = lean_box(v_res_2491_);
return v_r_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27(lean_object* v_00_u03b2_2493_, lean_object* v_data_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_data_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28(lean_object* v_00_u03b2_2496_, lean_object* v_a_2497_, lean_object* v_b_2498_, lean_object* v_x_2499_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28___redArg(v_a_2497_, v_b_2498_, v_x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2501_, lean_object* v_keys_2502_, lean_object* v_vals_2503_, lean_object* v_heq_2504_, lean_object* v_i_2505_, lean_object* v_k_2506_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2502_, v_i_2505_, v_k_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2508_, lean_object* v_keys_2509_, lean_object* v_vals_2510_, lean_object* v_heq_2511_, lean_object* v_i_2512_, lean_object* v_k_2513_){
_start:
{
uint8_t v_res_2514_; lean_object* v_r_2515_; 
v_res_2514_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2508_, v_keys_2509_, v_vals_2510_, v_heq_2511_, v_i_2512_, v_k_2513_);
lean_dec_ref(v_k_2513_);
lean_dec_ref(v_vals_2510_);
lean_dec_ref(v_keys_2509_);
v_r_2515_ = lean_box(v_res_2514_);
return v_r_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29(lean_object* v_00_u03b2_2516_, lean_object* v_i_2517_, lean_object* v_source_2518_, lean_object* v_target_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29___redArg(v_i_2517_, v_source_2518_, v_target_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30(lean_object* v_00_u03b2_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30___redArg(v_x_2522_, v_x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2525_, lean_object* v_decl_2526_, lean_object* v_ref_2527_){
_start:
{
lean_object* v_defValue_2529_; lean_object* v_descr_2530_; lean_object* v_deprecation_x3f_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v_defValue_2529_ = lean_ctor_get(v_decl_2526_, 0);
v_descr_2530_ = lean_ctor_get(v_decl_2526_, 1);
v_deprecation_x3f_2531_ = lean_ctor_get(v_decl_2526_, 2);
v___x_2532_ = lean_alloc_ctor(1, 0, 1);
v___x_2533_ = lean_unbox(v_defValue_2529_);
lean_ctor_set_uint8(v___x_2532_, 0, v___x_2533_);
lean_inc(v_deprecation_x3f_2531_);
lean_inc_ref(v_descr_2530_);
lean_inc_n(v_name_2525_, 2);
v___x_2534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2534_, 0, v_name_2525_);
lean_ctor_set(v___x_2534_, 1, v_ref_2527_);
lean_ctor_set(v___x_2534_, 2, v___x_2532_);
lean_ctor_set(v___x_2534_, 3, v_descr_2530_);
lean_ctor_set(v___x_2534_, 4, v_deprecation_x3f_2531_);
v___x_2535_ = lean_register_option(v_name_2525_, v___x_2534_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2543_; 
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v___x_2535_, 0);
lean_dec(v_unused_2544_);
v___x_2537_ = v___x_2535_;
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
else
{
lean_dec(v___x_2535_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_inc(v_defValue_2529_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v_name_2525_);
lean_ctor_set(v___x_2539_, 1, v_defValue_2529_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2539_);
v___x_2541_ = v___x_2537_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_name_2525_);
v_a_2545_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2535_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2535_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2553_, lean_object* v_decl_2554_, lean_object* v_ref_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2553_, v_decl_2554_, v_ref_2555_);
lean_dec_ref(v_decl_2554_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2572_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2573_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2574_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2575_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2572_, v___x_2573_, v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_ref_2584_; lean_object* v___x_2585_; lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2594_; 
v_ref_2584_ = lean_ctor_get(v___y_2581_, 2);
v___x_2585_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__7(v_msg_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2594_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2594_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
lean_inc(v_ref_2584_);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v_ref_2584_);
lean_ctor_set(v___x_2590_, 1, v_a_2586_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 1);
lean_ctor_set(v___x_2588_, 0, v___x_2590_);
v___x_2592_ = v___x_2588_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2601_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2610_ = l_Lean_stringToMessageData(v___x_2609_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2616_ = l_Lean_stringToMessageData(v___x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2617_, lean_object* v_expectedType_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v___x_2624_; 
lean_inc(v_a_2622_);
lean_inc_ref(v_a_2621_);
lean_inc(v_a_2620_);
lean_inc_ref(v_a_2619_);
lean_inc_ref(v_expr_2617_);
v___x_2624_ = lean_infer_type(v_expr_2617_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2626_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc_n(v_a_2625_, 2);
lean_dec_ref_known(v___x_2624_, 1);
v___x_2626_ = l_Lean_Meta_getLevel(v_a_2625_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
lean_inc_ref(v_expectedType_2618_);
v___x_2628_ = l_Lean_Meta_getLevel(v_expectedType_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v___x_2630_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2631_ = lean_box(0);
v___x_2632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2632_, 0, v_a_2629_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2633_, 0, v_a_2627_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
lean_inc_ref(v___x_2633_);
v___x_2634_ = l_Lean_mkConst(v___x_2630_, v___x_2633_);
v___x_2635_ = lean_unsigned_to_nat(3u);
v___x_2636_ = lean_mk_empty_array_with_capacity(v___x_2635_);
lean_inc(v_a_2625_);
v___x_2637_ = lean_array_push(v___x_2636_, v_a_2625_);
lean_inc_ref(v_expr_2617_);
v___x_2638_ = lean_array_push(v___x_2637_, v_expr_2617_);
lean_inc_ref(v_expectedType_2618_);
v___x_2639_ = lean_array_push(v___x_2638_, v_expectedType_2618_);
v___x_2640_ = l_Lean_mkAppN(v___x_2634_, v___x_2639_);
lean_dec_ref(v___x_2639_);
v___x_2641_ = lean_box(0);
v___x_2642_ = l_Lean_Meta_trySynthInstance(v___x_2640_, v___x_2641_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2740_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2740_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2740_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
switch(lean_obj_tag(v_a_2643_))
{
case 0:
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
lean_dec_ref_known(v___x_2633_, 2);
lean_dec(v_a_2625_);
lean_dec_ref(v_expectedType_2618_);
lean_dec_ref(v_expr_2617_);
v___x_2647_ = lean_box(0);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2647_);
v___x_2649_ = v___x_2645_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
case 1:
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2735_; 
lean_del_object(v___x_2645_);
v_a_2651_ = lean_ctor_get(v_a_2643_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_a_2643_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2653_ = v_a_2643_;
v_isShared_2654_ = v_isSharedCheck_2735_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v_a_2643_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2735_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2655_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2656_ = l_Lean_mkConst(v___x_2655_, v___x_2633_);
v___x_2657_ = lean_unsigned_to_nat(4u);
v___x_2658_ = lean_mk_empty_array_with_capacity(v___x_2657_);
v___x_2659_ = lean_array_push(v___x_2658_, v_a_2625_);
lean_inc_ref(v_expr_2617_);
v___x_2660_ = lean_array_push(v___x_2659_, v_expr_2617_);
lean_inc_ref(v_expectedType_2618_);
v___x_2661_ = lean_array_push(v___x_2660_, v_expectedType_2618_);
v___x_2662_ = lean_array_push(v___x_2661_, v_a_2651_);
v___x_2663_ = l_Lean_mkAppN(v___x_2656_, v___x_2662_);
lean_dec_ref(v___x_2662_);
v___x_2664_ = l_Lean_Meta_expandCoe(v___x_2663_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2726_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2726_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2726_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v_fst_2676_; lean_object* v___x_2677_; 
v_fst_2676_ = lean_ctor_get(v_a_2665_, 0);
lean_inc(v_a_2622_);
lean_inc_ref(v_a_2621_);
lean_inc(v_a_2620_);
lean_inc_ref(v_a_2619_);
lean_inc(v_fst_2676_);
v___x_2677_ = lean_infer_type(v_fst_2676_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2679_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2677_, 1);
lean_inc_ref(v_expectedType_2618_);
v___x_2679_ = l_Lean_Meta_isExprDefEq(v_a_2678_, v_expectedType_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; uint8_t v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2681_ = lean_unbox(v_a_2680_);
lean_dec(v_a_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2707_; 
lean_inc(v_fst_2676_);
lean_del_object(v___x_2667_);
lean_del_object(v___x_2653_);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_a_2665_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; lean_object* v_unused_2709_; 
v_unused_2708_ = lean_ctor_get(v_a_2665_, 1);
lean_dec(v_unused_2708_);
v_unused_2709_ = lean_ctor_get(v_a_2665_, 0);
lean_dec(v_unused_2709_);
v___x_2683_ = v_a_2665_;
v_isShared_2684_ = v_isSharedCheck_2707_;
goto v_resetjp_2682_;
}
else
{
lean_dec(v_a_2665_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2707_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2685_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2686_ = l_Lean_indentExpr(v_expr_2617_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set_tag(v___x_2683_, 7);
lean_ctor_set(v___x_2683_, 1, v___x_2686_);
lean_ctor_set(v___x_2683_, 0, v___x_2685_);
v___x_2688_ = v___x_2683_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
v___x_2689_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2688_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = l_Lean_indentExpr(v_expectedType_2618_);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = l_Lean_indentExpr(v_fst_2676_);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2696_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
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
}
else
{
lean_dec_ref(v_expectedType_2618_);
lean_dec_ref(v_expr_2617_);
goto v___jp_2669_;
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_del_object(v___x_2667_);
lean_dec(v_a_2665_);
lean_del_object(v___x_2653_);
lean_dec_ref(v_expectedType_2618_);
lean_dec_ref(v_expr_2617_);
v_a_2710_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2679_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2679_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_del_object(v___x_2667_);
lean_dec(v_a_2665_);
lean_del_object(v___x_2653_);
lean_dec_ref(v_expectedType_2618_);
lean_dec_ref(v_expr_2617_);
v_a_2718_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2677_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2677_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
v___jp_2669_:
{
lean_object* v___x_2671_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v_a_2665_);
v___x_2671_ = v___x_2653_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2665_);
v___x_2671_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2673_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2671_);
v___x_2673_ = v___x_2667_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_del_object(v___x_2653_);
lean_dec_ref(v_expectedType_2618_);
lean_dec_ref(v_expr_2617_);
v_a_2727_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2664_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2664_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
}
default: 
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_dec_ref_known(v___x_2633_, 2);
lean_dec(v_a_2625_);
lean_dec_ref(v_expectedType_2618_);
lean_dec_ref(v_expr_2617_);
v___x_2736_ = lean_box(2);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2736_);
v___x_2738_ = v___x_2645_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref_known(v___x_2633_, 2);
lean_dec(v_a_2625_);
lean_dec_ref(v_expectedType_2618_);
lean_dec_ref(v_expr_2617_);
v_a_2741_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2642_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2642_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec(v_a_2627_);
lean_dec(v_a_2625_);
lean_dec_ref(v_expectedType_2618_);
lean_dec_ref(v_expr_2617_);
v_a_2749_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2628_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2628_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_a_2625_);
lean_dec_ref(v_expectedType_2618_);
lean_dec_ref(v_expr_2617_);
v_a_2757_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2626_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2626_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec_ref(v_expectedType_2618_);
lean_dec_ref(v_expr_2617_);
v_a_2765_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2624_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2624_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2773_, lean_object* v_expectedType_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2773_, v_expectedType_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2781_, lean_object* v_msg_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2789_, lean_object* v_msg_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2789_, v_msg_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2797_, lean_object* v_expectedType_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2797_, v_expectedType_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2829_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2829_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2829_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
switch(lean_obj_tag(v_a_2805_))
{
case 0:
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2809_ = lean_box(0);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2809_);
v___x_2811_ = v___x_2807_;
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
case 1:
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2824_; 
v_a_2813_ = lean_ctor_get(v_a_2805_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_a_2805_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2815_ = v_a_2805_;
v_isShared_2816_ = v_isSharedCheck_2824_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v_a_2805_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2824_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_fst_2817_; lean_object* v___x_2819_; 
v_fst_2817_ = lean_ctor_get(v_a_2813_, 0);
lean_inc(v_fst_2817_);
lean_dec(v_a_2813_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v_fst_2817_);
v___x_2819_ = v___x_2815_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_fst_2817_);
v___x_2819_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2821_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2819_);
v___x_2821_ = v___x_2807_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
default: 
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2825_ = lean_box(2);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2825_);
v___x_2827_ = v___x_2807_;
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
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
v_a_2830_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2804_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2804_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2838_, lean_object* v_expectedType_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2838_, v_expectedType_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
return v_res_2845_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2854_ = l_Lean_stringToMessageData(v___x_2853_);
return v___x_2854_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2857_ = l_Lean_stringToMessageData(v___x_2856_);
return v___x_2857_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2860_ = l_Lean_stringToMessageData(v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v___x_2867_; 
lean_inc(v_a_2865_);
lean_inc_ref(v_a_2864_);
lean_inc(v_a_2863_);
lean_inc_ref(v_a_2862_);
lean_inc_ref(v_expr_2861_);
v___x_2867_ = lean_infer_type(v_expr_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2869_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc_n(v_a_2868_, 2);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = l_Lean_Meta_getLevel(v_a_2868_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___x_2871_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc_n(v_a_2872_, 2);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = l_Lean_mkSort(v_a_2872_);
lean_inc(v_a_2868_);
v___x_2874_ = l_Lean_mkArrow(v_a_2868_, v___x_2873_, v_a_2864_, v_a_2865_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_a_2875_);
v___x_2877_ = 0;
v___x_2878_ = lean_box(0);
v___x_2879_ = l_Lean_Meta_mkFreshExprMVar(v___x_2876_, v___x_2877_, v___x_2878_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc_n(v_a_2880_, 2);
lean_dec_ref_known(v___x_2879_, 1);
v___x_2881_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2882_ = lean_box(0);
v___x_2883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_a_2872_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2884_, 0, v_a_2870_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
lean_inc_ref(v___x_2884_);
v___x_2885_ = l_Lean_Expr_const___override(v___x_2881_, v___x_2884_);
lean_inc(v_a_2868_);
v___x_2886_ = l_Lean_mkAppB(v___x_2885_, v_a_2868_, v_a_2880_);
v___x_2887_ = lean_box(0);
v___x_2888_ = l_Lean_Meta_trySynthInstance(v___x_2886_, v___x_2887_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2975_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2891_ = v___x_2888_;
v_isShared_2892_ = v_isSharedCheck_2975_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2975_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
if (lean_obj_tag(v_a_2889_) == 1)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2971_; 
lean_del_object(v___x_2891_);
v_a_2893_ = lean_ctor_get(v_a_2889_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_a_2889_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2895_ = v_a_2889_;
v_isShared_2896_ = v_isSharedCheck_2971_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v_a_2889_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2971_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2897_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2898_ = l_Lean_Expr_const___override(v___x_2897_, v___x_2884_);
lean_inc_ref(v_expr_2861_);
lean_inc(v_a_2893_);
v___x_2899_ = l_Lean_mkApp4(v___x_2898_, v_a_2868_, v_a_2880_, v_a_2893_, v_expr_2861_);
v___x_2900_ = l_Lean_Meta_expandCoe(v___x_2899_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2962_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2962_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2962_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v_fst_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2960_; 
v_fst_2905_ = lean_ctor_get(v_a_2901_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_a_2901_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v_a_2901_, 1);
lean_dec(v_unused_2961_);
v___x_2907_ = v_a_2901_;
v_isShared_2908_ = v_isSharedCheck_2960_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_fst_2905_);
lean_dec(v_a_2901_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2960_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2916_; 
lean_inc(v_a_2865_);
lean_inc_ref(v_a_2864_);
lean_inc(v_a_2863_);
lean_inc_ref(v_a_2862_);
lean_inc(v_fst_2905_);
v___x_2916_ = lean_infer_type(v_fst_2905_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2918_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___x_2916_, 1);
lean_inc(v_a_2865_);
lean_inc_ref(v_a_2864_);
lean_inc(v_a_2863_);
lean_inc_ref(v_a_2862_);
v___x_2918_ = lean_whnf(v_a_2917_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; uint8_t v___x_2920_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
v___x_2920_ = l_Lean_Expr_isForall(v_a_2919_);
lean_dec(v_a_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
lean_del_object(v___x_2903_);
lean_del_object(v___x_2895_);
v___x_2921_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2922_ = l_Lean_indentExpr(v_expr_2861_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set_tag(v___x_2907_, 7);
lean_ctor_set(v___x_2907_, 1, v___x_2922_);
lean_ctor_set(v___x_2907_, 0, v___x_2921_);
v___x_2924_ = v___x_2907_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
v___x_2925_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = l_Lean_indentExpr(v_fst_2905_);
v___x_2928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2930_ = l_Lean_indentExpr(v_a_2893_);
v___x_2931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2929_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = l_Lean_MessageData_hint_x27(v___x_2931_);
v___x_2933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2928_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2933_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
else
{
lean_del_object(v___x_2907_);
lean_dec(v_a_2893_);
lean_dec_ref(v_expr_2861_);
goto v___jp_2909_;
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_del_object(v___x_2907_);
lean_dec(v_fst_2905_);
lean_del_object(v___x_2903_);
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_dec_ref(v_expr_2861_);
v_a_2944_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2918_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2918_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_del_object(v___x_2907_);
lean_dec(v_fst_2905_);
lean_del_object(v___x_2903_);
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_dec_ref(v_expr_2861_);
v_a_2952_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2916_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2916_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
v___jp_2909_:
{
lean_object* v___x_2911_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v_fst_2905_);
v___x_2911_ = v___x_2895_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_fst_2905_);
v___x_2911_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2913_; 
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2911_);
v___x_2913_ = v___x_2903_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_dec_ref(v_expr_2861_);
v_a_2963_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2900_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2900_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
else
{
lean_object* v___x_2973_; 
lean_dec(v_a_2889_);
lean_dec_ref_known(v___x_2884_, 2);
lean_dec(v_a_2880_);
lean_dec(v_a_2868_);
lean_dec_ref(v_expr_2861_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2887_);
v___x_2973_ = v___x_2891_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2887_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec_ref_known(v___x_2884_, 2);
lean_dec(v_a_2880_);
lean_dec(v_a_2868_);
lean_dec_ref(v_expr_2861_);
v_a_2976_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2888_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2888_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_a_2872_);
lean_dec(v_a_2870_);
lean_dec(v_a_2868_);
lean_dec_ref(v_expr_2861_);
v_a_2984_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2879_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2879_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec(v_a_2872_);
lean_dec(v_a_2870_);
lean_dec(v_a_2868_);
lean_dec_ref(v_expr_2861_);
v_a_2992_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2874_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2874_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec(v_a_2870_);
lean_dec(v_a_2868_);
lean_dec_ref(v_expr_2861_);
v_a_3000_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2871_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2871_);
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
lean_dec(v_a_2868_);
lean_dec_ref(v_expr_2861_);
v_a_3008_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2869_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2869_);
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
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref(v_expr_2861_);
v_a_3016_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2867_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2867_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
return v_res_3030_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_3039_ = l_Lean_stringToMessageData(v___x_3038_);
return v___x_3039_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_3042_ = l_Lean_stringToMessageData(v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v___x_3049_; 
lean_inc(v_a_3047_);
lean_inc_ref(v_a_3046_);
lean_inc(v_a_3045_);
lean_inc_ref(v_a_3044_);
lean_inc_ref(v_expr_3043_);
v___x_3049_ = lean_infer_type(v_expr_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3051_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc_n(v_a_3050_, 2);
lean_dec_ref_known(v___x_3049_, 1);
v___x_3051_ = l_Lean_Meta_getLevel(v_a_3050_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3053_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref_known(v___x_3051_, 1);
v___x_3053_ = l_Lean_Meta_mkFreshLevelMVar(v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc_n(v_a_3054_, 2);
lean_dec_ref_known(v___x_3053_, 1);
v___x_3055_ = l_Lean_mkSort(v_a_3054_);
v___x_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
v___x_3057_ = 0;
v___x_3058_ = lean_box(0);
v___x_3059_ = l_Lean_Meta_mkFreshExprMVar(v___x_3056_, v___x_3057_, v___x_3058_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc_n(v_a_3060_, 2);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_3062_ = lean_box(0);
v___x_3063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3063_, 0, v_a_3054_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3064_, 0, v_a_3052_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
lean_inc_ref(v___x_3064_);
v___x_3065_ = l_Lean_Expr_const___override(v___x_3061_, v___x_3064_);
lean_inc(v_a_3050_);
v___x_3066_ = l_Lean_mkAppB(v___x_3065_, v_a_3050_, v_a_3060_);
v___x_3067_ = lean_box(0);
v___x_3068_ = l_Lean_Meta_trySynthInstance(v___x_3066_, v___x_3067_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3155_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3155_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3155_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
if (lean_obj_tag(v_a_3069_) == 1)
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3151_; 
lean_del_object(v___x_3071_);
v_a_3073_ = lean_ctor_get(v_a_3069_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_a_3069_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3075_ = v_a_3069_;
v_isShared_3076_ = v_isSharedCheck_3151_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v_a_3069_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3151_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3077_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_3078_ = l_Lean_Expr_const___override(v___x_3077_, v___x_3064_);
lean_inc_ref(v_expr_3043_);
lean_inc(v_a_3073_);
v___x_3079_ = l_Lean_mkApp4(v___x_3078_, v_a_3050_, v_a_3060_, v_a_3073_, v_expr_3043_);
v___x_3080_ = l_Lean_Meta_expandCoe(v___x_3079_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3142_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3142_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3142_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v_fst_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3140_; 
v_fst_3085_ = lean_ctor_get(v_a_3081_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_a_3081_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v_a_3081_, 1);
lean_dec(v_unused_3141_);
v___x_3087_ = v_a_3081_;
v_isShared_3088_ = v_isSharedCheck_3140_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_fst_3085_);
lean_dec(v_a_3081_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3140_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3096_; 
lean_inc(v_a_3047_);
lean_inc_ref(v_a_3046_);
lean_inc(v_a_3045_);
lean_inc_ref(v_a_3044_);
lean_inc(v_fst_3085_);
v___x_3096_ = lean_infer_type(v_fst_3085_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3098_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref_known(v___x_3096_, 1);
lean_inc(v_a_3047_);
lean_inc_ref(v_a_3046_);
lean_inc(v_a_3045_);
lean_inc_ref(v_a_3044_);
v___x_3098_ = lean_whnf(v_a_3097_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; uint8_t v___x_3100_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3099_);
lean_dec_ref_known(v___x_3098_, 1);
v___x_3100_ = l_Lean_Expr_isSort(v_a_3099_);
lean_dec(v_a_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
lean_del_object(v___x_3083_);
lean_del_object(v___x_3075_);
v___x_3101_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3102_ = l_Lean_indentExpr(v_expr_3043_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set_tag(v___x_3087_, 7);
lean_ctor_set(v___x_3087_, 1, v___x_3102_);
lean_ctor_set(v___x_3087_, 0, v___x_3101_);
v___x_3104_ = v___x_3087_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
v___x_3105_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3104_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = l_Lean_indentExpr(v_fst_3085_);
v___x_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3110_ = l_Lean_indentExpr(v_a_3073_);
v___x_3111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3109_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = l_Lean_MessageData_hint_x27(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3108_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3113_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_del_object(v___x_3087_);
lean_dec(v_a_3073_);
lean_dec_ref(v_expr_3043_);
goto v___jp_3089_;
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_del_object(v___x_3087_);
lean_dec(v_fst_3085_);
lean_del_object(v___x_3083_);
lean_del_object(v___x_3075_);
lean_dec(v_a_3073_);
lean_dec_ref(v_expr_3043_);
v_a_3124_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3098_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3098_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_del_object(v___x_3087_);
lean_dec(v_fst_3085_);
lean_del_object(v___x_3083_);
lean_del_object(v___x_3075_);
lean_dec(v_a_3073_);
lean_dec_ref(v_expr_3043_);
v_a_3132_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3096_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3096_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
v___jp_3089_:
{
lean_object* v___x_3091_; 
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 0, v_fst_3085_);
v___x_3091_ = v___x_3075_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_fst_3085_);
v___x_3091_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3093_; 
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3091_);
v___x_3093_ = v___x_3083_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_del_object(v___x_3075_);
lean_dec(v_a_3073_);
lean_dec_ref(v_expr_3043_);
v_a_3143_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3080_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3080_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
else
{
lean_object* v___x_3153_; 
lean_dec(v_a_3069_);
lean_dec_ref_known(v___x_3064_, 2);
lean_dec(v_a_3060_);
lean_dec(v_a_3050_);
lean_dec_ref(v_expr_3043_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 0, v___x_3067_);
v___x_3153_ = v___x_3071_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3067_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref_known(v___x_3064_, 2);
lean_dec(v_a_3060_);
lean_dec(v_a_3050_);
lean_dec_ref(v_expr_3043_);
v_a_3156_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3068_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3068_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_a_3054_);
lean_dec(v_a_3052_);
lean_dec(v_a_3050_);
lean_dec_ref(v_expr_3043_);
v_a_3164_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3059_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3059_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec(v_a_3052_);
lean_dec(v_a_3050_);
lean_dec_ref(v_expr_3043_);
v_a_3172_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3053_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3053_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v_a_3050_);
lean_dec_ref(v_expr_3043_);
v_a_3180_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3051_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3051_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec_ref(v_expr_3043_);
v_a_3188_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3049_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3049_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3203_, lean_object* v___y_3204_){
_start:
{
uint8_t v___x_3206_; 
v___x_3206_ = l_Lean_Expr_hasMVar(v_e_3203_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_e_3203_);
return v___x_3207_;
}
else
{
lean_object* v___x_3208_; lean_object* v_mctx_3209_; lean_object* v___x_3210_; lean_object* v_fst_3211_; lean_object* v_snd_3212_; lean_object* v___x_3213_; lean_object* v_cache_3214_; lean_object* v_zetaDeltaFVarIds_3215_; lean_object* v_postponed_3216_; lean_object* v_diag_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3226_; 
v___x_3208_ = lean_st_ref_get(v___y_3204_);
v_mctx_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc_ref(v_mctx_3209_);
lean_dec(v___x_3208_);
v___x_3210_ = l_Lean_instantiateMVarsCore(v_mctx_3209_, v_e_3203_);
v_fst_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_fst_3211_);
v_snd_3212_ = lean_ctor_get(v___x_3210_, 1);
lean_inc(v_snd_3212_);
lean_dec_ref(v___x_3210_);
v___x_3213_ = lean_st_ref_take(v___y_3204_);
v_cache_3214_ = lean_ctor_get(v___x_3213_, 1);
v_zetaDeltaFVarIds_3215_ = lean_ctor_get(v___x_3213_, 2);
v_postponed_3216_ = lean_ctor_get(v___x_3213_, 3);
v_diag_3217_ = lean_ctor_get(v___x_3213_, 4);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v___x_3213_, 0);
lean_dec(v_unused_3227_);
v___x_3219_ = v___x_3213_;
v_isShared_3220_ = v_isSharedCheck_3226_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_diag_3217_);
lean_inc(v_postponed_3216_);
lean_inc(v_zetaDeltaFVarIds_3215_);
lean_inc(v_cache_3214_);
lean_dec(v___x_3213_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3226_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v_snd_3212_);
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_snd_3212_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_cache_3214_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_zetaDeltaFVarIds_3215_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_postponed_3216_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_diag_3217_);
v___x_3222_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_st_ref_put(v___y_3204_, v___x_3222_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_fst_3211_);
return v___x_3224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3228_, v___y_3229_);
lean_dec(v___y_3229_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3232_, v___y_3234_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v___y_3253_; lean_object* v___x_3292_; uint8_t v_transparency_3293_; uint8_t v___x_3294_; uint8_t v___x_3295_; 
v___x_3292_ = l_Lean_Meta_Context_config(v_a_3247_);
v_transparency_3293_ = lean_ctor_get_uint8(v___x_3292_, 9);
lean_dec_ref(v___x_3292_);
v___x_3294_ = 2;
v___x_3295_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3293_, v___x_3294_);
if (v___x_3295_ == 0)
{
lean_object* v_keyedConfig_3296_; uint8_t v_trackZetaDelta_3297_; lean_object* v_zetaDeltaSet_3298_; lean_object* v_lctx_3299_; lean_object* v_localInstances_3300_; lean_object* v_defEqCtx_x3f_3301_; lean_object* v_synthPendingDepth_3302_; lean_object* v_customCanUnfoldPredicate_x3f_3303_; uint8_t v_univApprox_3304_; uint8_t v_inTypeClassResolution_3305_; uint8_t v_cacheInferType_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_keyedConfig_3296_ = lean_ctor_get(v_a_3247_, 0);
v_trackZetaDelta_3297_ = lean_ctor_get_uint8(v_a_3247_, sizeof(void*)*7);
v_zetaDeltaSet_3298_ = lean_ctor_get(v_a_3247_, 1);
v_lctx_3299_ = lean_ctor_get(v_a_3247_, 2);
v_localInstances_3300_ = lean_ctor_get(v_a_3247_, 3);
v_defEqCtx_x3f_3301_ = lean_ctor_get(v_a_3247_, 4);
v_synthPendingDepth_3302_ = lean_ctor_get(v_a_3247_, 5);
v_customCanUnfoldPredicate_x3f_3303_ = lean_ctor_get(v_a_3247_, 6);
v_univApprox_3304_ = lean_ctor_get_uint8(v_a_3247_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3305_ = lean_ctor_get_uint8(v_a_3247_, sizeof(void*)*7 + 2);
v_cacheInferType_3306_ = lean_ctor_get_uint8(v_a_3247_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3296_);
v___x_3307_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3294_, v_keyedConfig_3296_);
lean_inc(v_customCanUnfoldPredicate_x3f_3303_);
lean_inc(v_synthPendingDepth_3302_);
lean_inc(v_defEqCtx_x3f_3301_);
lean_inc_ref(v_localInstances_3300_);
lean_inc_ref(v_lctx_3299_);
lean_inc(v_zetaDeltaSet_3298_);
v___x_3308_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
lean_ctor_set(v___x_3308_, 1, v_zetaDeltaSet_3298_);
lean_ctor_set(v___x_3308_, 2, v_lctx_3299_);
lean_ctor_set(v___x_3308_, 3, v_localInstances_3300_);
lean_ctor_set(v___x_3308_, 4, v_defEqCtx_x3f_3301_);
lean_ctor_set(v___x_3308_, 5, v_synthPendingDepth_3302_);
lean_ctor_set(v___x_3308_, 6, v_customCanUnfoldPredicate_x3f_3303_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*7, v_trackZetaDelta_3297_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*7 + 1, v_univApprox_3304_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3305_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*7 + 3, v_cacheInferType_3306_);
lean_inc(v_a_3250_);
lean_inc_ref(v_a_3249_);
lean_inc(v_a_3248_);
v___x_3309_ = lean_whnf(v_type_3246_, v___x_3308_, v_a_3248_, v_a_3249_, v_a_3250_);
v___y_3253_ = v___x_3309_;
goto v___jp_3252_;
}
else
{
lean_object* v___x_3310_; 
lean_inc(v_a_3250_);
lean_inc_ref(v_a_3249_);
lean_inc(v_a_3248_);
lean_inc_ref(v_a_3247_);
v___x_3310_ = lean_whnf(v_type_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
v___y_3253_ = v___x_3310_;
goto v___jp_3252_;
}
v___jp_3252_:
{
if (lean_obj_tag(v___y_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3283_; 
v_a_3254_ = lean_ctor_get(v___y_3253_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___y_3253_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3256_ = v___y_3253_;
v_isShared_3257_ = v_isSharedCheck_3283_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___y_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3283_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
if (lean_obj_tag(v_a_3254_) == 5)
{
lean_object* v_fn_3258_; lean_object* v_arg_3259_; lean_object* v___x_3260_; lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3278_; 
lean_del_object(v___x_3256_);
v_fn_3258_ = lean_ctor_get(v_a_3254_, 0);
lean_inc_ref(v_fn_3258_);
v_arg_3259_ = lean_ctor_get(v_a_3254_, 1);
lean_inc_ref(v_arg_3259_);
lean_dec_ref_known(v_a_3254_, 2);
v___x_3260_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3258_, v_a_3248_);
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3278_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3278_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3277_; 
v___x_3265_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3259_, v_a_3248_);
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3277_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3277_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v_a_3261_);
lean_ctor_set(v___x_3270_, 1, v_a_3266_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set_tag(v___x_3263_, 1);
lean_ctor_set(v___x_3263_, 0, v___x_3270_);
v___x_3272_ = v___x_3263_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3274_; 
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3272_);
v___x_3274_ = v___x_3268_;
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
}
}
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
lean_dec(v_a_3254_);
v___x_3279_ = lean_box(0);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3279_);
v___x_3281_ = v___x_3256_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
v_a_3284_ = lean_ctor_get(v___y_3253_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___y_3253_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___y_3253_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___y_3253_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_Meta_isTypeApp_x3f(v_type_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_Meta_isTypeApp_x3f(v_type_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3360_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3327_ = v___x_3324_;
v_isShared_3328_ = v_isSharedCheck_3360_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3360_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
if (lean_obj_tag(v_a_3325_) == 1)
{
lean_object* v_val_3329_; lean_object* v_fst_3330_; lean_object* v___x_3331_; 
lean_del_object(v___x_3327_);
v_val_3329_ = lean_ctor_get(v_a_3325_, 0);
lean_inc(v_val_3329_);
lean_dec_ref_known(v_a_3325_, 1);
v_fst_3330_ = lean_ctor_get(v_val_3329_, 0);
lean_inc(v_fst_3330_);
lean_dec(v_val_3329_);
v___x_3331_ = l_Lean_Meta_isMonad_x3f(v_fst_3330_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3346_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3346_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3346_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
if (lean_obj_tag(v_a_3332_) == 0)
{
uint8_t v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3336_ = 0;
v___x_3337_ = lean_box(v___x_3336_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3337_);
v___x_3339_ = v___x_3334_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
else
{
uint8_t v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
lean_dec_ref_known(v_a_3332_, 1);
v___x_3341_ = 1;
v___x_3342_ = lean_box(v___x_3341_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3342_);
v___x_3344_ = v___x_3334_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
v_a_3347_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3331_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3331_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
else
{
uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3358_; 
lean_dec(v_a_3325_);
v___x_3355_ = 0;
v___x_3356_ = lean_box(v___x_3355_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v___x_3356_);
v___x_3358_ = v___x_3327_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
v_a_3361_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3324_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3324_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_Meta_isMonadApp(v_type_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
lean_dec(v_a_3373_);
lean_dec_ref(v_a_3372_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
return v_res_3375_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3376_, lean_object* v_opt_3377_){
_start:
{
lean_object* v_name_3378_; lean_object* v_defValue_3379_; lean_object* v_map_3380_; lean_object* v___x_3381_; 
v_name_3378_ = lean_ctor_get(v_opt_3377_, 0);
v_defValue_3379_ = lean_ctor_get(v_opt_3377_, 1);
v_map_3380_ = lean_ctor_get(v_opts_3376_, 0);
v___x_3381_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3380_, v_name_3378_);
if (lean_obj_tag(v___x_3381_) == 0)
{
uint8_t v___x_3382_; 
v___x_3382_ = lean_unbox(v_defValue_3379_);
return v___x_3382_;
}
else
{
lean_object* v_val_3383_; 
v_val_3383_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_val_3383_);
lean_dec_ref_known(v___x_3381_, 1);
if (lean_obj_tag(v_val_3383_) == 1)
{
uint8_t v_v_3384_; 
v_v_3384_ = lean_ctor_get_uint8(v_val_3383_, 0);
lean_dec_ref_known(v_val_3383_, 0);
return v_v_3384_;
}
else
{
uint8_t v___x_3385_; 
lean_dec(v_val_3383_);
v___x_3385_ = lean_unbox(v_defValue_3379_);
return v___x_3385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3386_, lean_object* v_opt_3387_){
_start:
{
uint8_t v_res_3388_; lean_object* v_r_3389_; 
v_res_3388_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3386_, v_opt_3387_);
lean_dec_ref(v_opt_3387_);
lean_dec_ref(v_opts_3386_);
v_r_3389_ = lean_box(v_res_3388_);
return v_r_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v_x_3400_);
return v_res_3406_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = lean_unsigned_to_nat(0u);
v___x_3417_ = l_Lean_mkBVar(v___x_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3429_, lean_object* v_expectedType_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_){
_start:
{
lean_object* v_a_3437_; lean_object* v___y_3445_; lean_object* v___x_3455_; lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3859_; 
v___x_3455_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3430_, v_a_3432_);
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3859_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3859_;
goto v_resetjp_3457_;
}
v___jp_3436_:
{
uint8_t v___x_3438_; 
v___x_3438_ = l_Lean_Exception_isInterrupt(v_a_3437_);
if (v___x_3438_ == 0)
{
uint8_t v___x_3439_; 
lean_inc_ref(v_a_3437_);
v___x_3439_ = l_Lean_Exception_isRuntime(v_a_3437_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec_ref(v_a_3437_);
v___x_3440_ = lean_box(0);
v___x_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
return v___x_3441_;
}
else
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v_a_3437_);
return v___x_3442_;
}
}
else
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3443_, 0, v_a_3437_);
return v___x_3443_;
}
}
v___jp_3444_:
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3454_; 
v_a_3446_ = lean_ctor_get(v___y_3445_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___y_3445_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3448_ = v___y_3445_;
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___y_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v_a_3450_; lean_object* v___x_3452_; 
v_a_3450_ = lean_ctor_get(v_a_3446_, 0);
lean_inc(v_a_3450_);
lean_dec(v_a_3446_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v_a_3450_);
v___x_3452_ = v___x_3448_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; 
lean_inc(v_a_3434_);
lean_inc_ref(v_a_3433_);
lean_inc(v_a_3432_);
lean_inc_ref(v_a_3431_);
lean_inc_ref(v_e_3429_);
v___x_3460_ = lean_infer_type(v_e_3429_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3850_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v___x_3462_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3461_, v_a_3432_);
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3850_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3850_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; 
lean_inc(v_a_3456_);
v___x_3467_ = l_Lean_Meta_isTypeApp_x3f(v_a_3456_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3841_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3841_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3841_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
if (lean_obj_tag(v_a_3468_) == 1)
{
lean_object* v_val_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3836_; 
lean_del_object(v___x_3470_);
v_val_3472_ = lean_ctor_get(v_a_3468_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_a_3468_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3474_ = v_a_3468_;
v_isShared_3475_ = v_isSharedCheck_3836_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_val_3472_);
lean_dec(v_a_3468_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3836_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v_fst_3476_; lean_object* v_snd_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3835_; 
v_fst_3476_ = lean_ctor_get(v_val_3472_, 0);
v_snd_3477_ = lean_ctor_get(v_val_3472_, 1);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_val_3472_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3479_ = v_val_3472_;
v_isShared_3480_ = v_isSharedCheck_3835_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_snd_3477_);
lean_inc(v_fst_3476_);
lean_dec(v_val_3472_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3835_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; 
lean_inc(v_a_3463_);
v___x_3481_ = l_Lean_Meta_isTypeApp_x3f(v_a_3463_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3826_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3826_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3826_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
if (lean_obj_tag(v_a_3482_) == 1)
{
lean_object* v_val_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3821_; 
lean_del_object(v___x_3484_);
v_val_3486_ = lean_ctor_get(v_a_3482_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_a_3482_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3488_ = v_a_3482_;
v_isShared_3489_ = v_isSharedCheck_3821_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_val_3486_);
lean_dec(v_a_3482_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3821_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v_fst_3490_; lean_object* v_snd_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3820_; 
v_fst_3490_ = lean_ctor_get(v_val_3486_, 0);
v_snd_3491_ = lean_ctor_get(v_val_3486_, 1);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_val_3486_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3493_ = v_val_3486_;
v_isShared_3494_ = v_isSharedCheck_3820_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_snd_3491_);
lean_inc(v_fst_3490_);
lean_dec(v_val_3486_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3820_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_Meta_saveState___redArg(v_a_3432_, v_a_3434_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
lean_inc(v_fst_3476_);
lean_inc(v_fst_3490_);
v___x_3497_ = l_Lean_Meta_isExprDefEq(v_fst_3490_, v_fst_3476_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3803_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3803_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3803_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
uint8_t v___x_3502_; 
v___x_3502_ = lean_unbox(v_a_3498_);
lean_dec(v_a_3498_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
lean_dec(v_a_3496_);
lean_del_object(v___x_3474_);
lean_del_object(v___x_3465_);
lean_del_object(v___x_3458_);
v___x_3503_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3433_);
v___x_3504_ = l_Lean_Meta_autoLift;
v___x_3505_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v___x_3503_, v___x_3504_);
lean_dec_ref(v___x_3503_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v___x_3506_ = lean_box(0);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v___x_3506_);
v___x_3508_ = v___x_3500_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
else
{
lean_object* v___x_3510_; 
lean_del_object(v___x_3500_);
lean_inc(v_a_3434_);
lean_inc_ref(v_a_3433_);
lean_inc(v_a_3432_);
lean_inc_ref(v_a_3431_);
lean_inc(v_fst_3490_);
v___x_3510_ = lean_infer_type(v_fst_3490_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3512_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
lean_inc(v_a_3434_);
lean_inc_ref(v_a_3433_);
lean_inc(v_a_3432_);
lean_inc_ref(v_a_3431_);
v___x_3512_ = lean_whnf(v_a_3511_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
if (lean_obj_tag(v_a_3513_) == 7)
{
lean_object* v_binderType_3514_; 
v_binderType_3514_ = lean_ctor_get(v_a_3513_, 1);
if (lean_obj_tag(v_binderType_3514_) == 3)
{
lean_object* v_body_3515_; 
v_body_3515_ = lean_ctor_get(v_a_3513_, 2);
if (lean_obj_tag(v_body_3515_) == 3)
{
lean_object* v_u_3516_; lean_object* v_u_3517_; lean_object* v___x_3518_; 
lean_inc_ref(v_body_3515_);
lean_inc_ref(v_binderType_3514_);
lean_dec_ref_known(v_a_3513_, 3);
v_u_3516_ = lean_ctor_get(v_binderType_3514_, 0);
lean_inc(v_u_3516_);
lean_dec_ref_known(v_binderType_3514_, 1);
v_u_3517_ = lean_ctor_get(v_body_3515_, 0);
lean_inc(v_u_3517_);
lean_dec_ref_known(v_body_3515_, 1);
lean_inc(v_a_3434_);
lean_inc_ref(v_a_3433_);
lean_inc(v_a_3432_);
lean_inc_ref(v_a_3431_);
lean_inc(v_fst_3476_);
v___x_3518_ = lean_infer_type(v_fst_3476_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3520_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
lean_inc(v_a_3434_);
lean_inc_ref(v_a_3433_);
lean_inc(v_a_3432_);
lean_inc_ref(v_a_3431_);
v___x_3520_ = lean_whnf(v_a_3519_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
if (lean_obj_tag(v_a_3521_) == 7)
{
lean_object* v_binderType_3522_; 
v_binderType_3522_ = lean_ctor_get(v_a_3521_, 1);
if (lean_obj_tag(v_binderType_3522_) == 3)
{
lean_object* v_body_3523_; 
v_body_3523_ = lean_ctor_get(v_a_3521_, 2);
if (lean_obj_tag(v_body_3523_) == 3)
{
lean_object* v_u_3524_; lean_object* v_u_3525_; lean_object* v___x_3526_; 
lean_inc_ref(v_body_3523_);
lean_inc_ref(v_binderType_3522_);
lean_dec_ref_known(v_a_3521_, 3);
v_u_3524_ = lean_ctor_get(v_binderType_3522_, 0);
lean_inc(v_u_3524_);
lean_dec_ref_known(v_binderType_3522_, 1);
v_u_3525_ = lean_ctor_get(v_body_3523_, 0);
lean_inc(v_u_3525_);
lean_dec_ref_known(v_body_3523_, 1);
v___x_3526_ = l_Lean_Meta_decLevel(v_u_3516_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___x_3528_ = l_Lean_Meta_decLevel(v_u_3524_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
lean_inc(v_a_3527_);
v___x_3530_ = l_Lean_Meta_isLevelDefEq(v_a_3527_, v_a_3529_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3695_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3695_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3695_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
uint8_t v___x_3535_; 
v___x_3535_ = lean_unbox(v_a_3531_);
lean_dec(v_a_3531_);
if (v___x_3535_ == 1)
{
lean_object* v___x_3536_; 
lean_del_object(v___x_3533_);
v___x_3536_ = l_Lean_Meta_decLevel(v_u_3517_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = l_Lean_Meta_decLevel(v_u_3525_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref_known(v___x_3538_, 1);
v___x_3540_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3541_ = lean_box(0);
if (v_isShared_3494_ == 0)
{
lean_ctor_set_tag(v___x_3493_, 1);
lean_ctor_set(v___x_3493_, 1, v___x_3541_);
lean_ctor_set(v___x_3493_, 0, v_a_3539_);
v___x_3543_ = v___x_3493_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3539_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3545_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set_tag(v___x_3479_, 1);
lean_ctor_set(v___x_3479_, 1, v___x_3543_);
lean_ctor_set(v___x_3479_, 0, v_a_3537_);
v___x_3545_ = v___x_3479_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3537_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3546_, 0, v_a_3527_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = l_Lean_Expr_const___override(v___x_3540_, v___x_3546_);
v___x_3548_ = lean_unsigned_to_nat(2u);
v___x_3549_ = lean_mk_empty_array_with_capacity(v___x_3548_);
lean_inc(v_fst_3490_);
v___x_3550_ = lean_array_push(v___x_3549_, v_fst_3490_);
lean_inc(v_fst_3476_);
v___x_3551_ = lean_array_push(v___x_3550_, v_fst_3476_);
v___x_3552_ = l_Lean_mkAppN(v___x_3547_, v___x_3551_);
lean_dec_ref(v___x_3551_);
v___x_3553_ = lean_box(0);
v___x_3554_ = l_Lean_Meta_trySynthInstance(v___x_3552_, v___x_3553_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3685_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3685_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3685_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
if (lean_obj_tag(v_a_3555_) == 1)
{
lean_object* v_a_3559_; lean_object* v___x_3560_; 
lean_del_object(v___x_3557_);
v_a_3559_ = lean_ctor_get(v_a_3555_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v_a_3555_, 1);
lean_inc(v_snd_3491_);
v___x_3560_ = l_Lean_Meta_getDecLevel(v_snd_3491_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v___x_3562_ = l_Lean_Meta_getDecLevel(v_a_3463_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3564_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
lean_dec_ref_known(v___x_3562_, 1);
lean_inc(v_a_3456_);
v___x_3564_ = l_Lean_Meta_getDecLevel(v_a_3456_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3564_, 1);
v___x_3566_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3567_, 0, v_a_3565_);
lean_ctor_set(v___x_3567_, 1, v___x_3541_);
v___x_3568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3568_, 0, v_a_3563_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3569_, 0, v_a_3561_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
lean_inc_ref(v___x_3569_);
v___x_3570_ = l_Lean_mkConst(v___x_3566_, v___x_3569_);
v___x_3571_ = lean_unsigned_to_nat(5u);
v___x_3572_ = lean_mk_empty_array_with_capacity(v___x_3571_);
lean_inc(v_fst_3490_);
v___x_3573_ = lean_array_push(v___x_3572_, v_fst_3490_);
lean_inc(v_fst_3476_);
v___x_3574_ = lean_array_push(v___x_3573_, v_fst_3476_);
lean_inc(v_a_3559_);
v___x_3575_ = lean_array_push(v___x_3574_, v_a_3559_);
lean_inc(v_snd_3491_);
v___x_3576_ = lean_array_push(v___x_3575_, v_snd_3491_);
lean_inc_ref(v_e_3429_);
v___x_3577_ = lean_array_push(v___x_3576_, v_e_3429_);
v___x_3578_ = l_Lean_mkAppN(v___x_3570_, v___x_3577_);
lean_dec_ref(v___x_3577_);
lean_inc(v_a_3434_);
lean_inc_ref(v_a_3433_);
lean_inc(v_a_3432_);
lean_inc_ref(v_a_3431_);
lean_inc_ref(v___x_3578_);
v___x_3579_ = lean_infer_type(v___x_3578_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3581_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
lean_inc(v_a_3456_);
v___x_3581_ = l_Lean_Meta_isExprDefEq(v_a_3456_, v_a_3580_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3676_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3676_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3676_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_unbox(v_a_3582_);
lean_dec(v_a_3582_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; 
lean_del_object(v___x_3584_);
lean_dec_ref(v___x_3578_);
lean_del_object(v___x_3488_);
lean_inc(v_fst_3476_);
v___x_3587_ = l_Lean_Meta_isMonad_x3f(v_fst_3476_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3668_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3590_ = v___x_3587_;
v_isShared_3591_ = v_isSharedCheck_3668_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3587_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3668_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
if (lean_obj_tag(v_a_3588_) == 1)
{
lean_object* v_val_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3664_; 
lean_del_object(v___x_3590_);
v_val_3592_ = lean_ctor_get(v_a_3588_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_a_3588_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3594_ = v_a_3588_;
v_isShared_3595_ = v_isSharedCheck_3664_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_val_3592_);
lean_dec(v_a_3588_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3664_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; 
lean_inc(v_snd_3491_);
v___x_3596_ = l_Lean_Meta_getLevel(v_snd_3491_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3598_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3596_, 1);
lean_inc(v_snd_3477_);
v___x_3598_ = l_Lean_Meta_getLevel(v_snd_3477_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3601_ = 0;
v___x_3602_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3603_, 0, v_a_3599_);
lean_ctor_set(v___x_3603_, 1, v___x_3541_);
v___x_3604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3604_, 0, v_a_3597_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = l_Lean_mkConst(v___x_3602_, v___x_3604_);
v___x_3606_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3607_ = lean_unsigned_to_nat(3u);
v___x_3608_ = lean_mk_empty_array_with_capacity(v___x_3607_);
lean_inc_n(v_snd_3491_, 2);
v___x_3609_ = lean_array_push(v___x_3608_, v_snd_3491_);
v___x_3610_ = lean_array_push(v___x_3609_, v___x_3606_);
lean_inc(v_snd_3477_);
v___x_3611_ = lean_array_push(v___x_3610_, v_snd_3477_);
v___x_3612_ = l_Lean_mkAppN(v___x_3605_, v___x_3611_);
lean_dec_ref(v___x_3611_);
v___x_3613_ = l_Lean_mkForall(v___x_3600_, v___x_3601_, v_snd_3491_, v___x_3612_);
v___x_3614_ = l_Lean_Meta_trySynthInstance(v___x_3613_, v___x_3553_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3660_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3660_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3660_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
if (lean_obj_tag(v_a_3615_) == 1)
{
lean_object* v_a_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
lean_del_object(v___x_3617_);
v_a_3619_ = lean_ctor_get(v_a_3615_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v_a_3615_, 1);
v___x_3620_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3621_ = l_Lean_mkConst(v___x_3620_, v___x_3569_);
v___x_3622_ = lean_unsigned_to_nat(8u);
v___x_3623_ = lean_mk_empty_array_with_capacity(v___x_3622_);
v___x_3624_ = lean_array_push(v___x_3623_, v_fst_3490_);
v___x_3625_ = lean_array_push(v___x_3624_, v_fst_3476_);
v___x_3626_ = lean_array_push(v___x_3625_, v_snd_3491_);
v___x_3627_ = lean_array_push(v___x_3626_, v_snd_3477_);
v___x_3628_ = lean_array_push(v___x_3627_, v_a_3559_);
v___x_3629_ = lean_array_push(v___x_3628_, v_a_3619_);
v___x_3630_ = lean_array_push(v___x_3629_, v_val_3592_);
v___x_3631_ = lean_array_push(v___x_3630_, v_e_3429_);
v___x_3632_ = l_Lean_mkAppN(v___x_3621_, v___x_3631_);
lean_dec_ref(v___x_3631_);
v___x_3633_ = l_Lean_Meta_expandCoe(v___x_3632_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v_fst_3635_; lean_object* v___x_3636_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v_fst_3635_ = lean_ctor_get(v_a_3634_, 0);
lean_inc_n(v_fst_3635_, 2);
lean_dec(v_a_3634_);
lean_inc(v_a_3434_);
lean_inc_ref(v_a_3433_);
lean_inc(v_a_3432_);
lean_inc_ref(v_a_3431_);
v___x_3636_ = lean_infer_type(v_fst_3635_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3638_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v___x_3638_ = l_Lean_Meta_isExprDefEq(v_a_3456_, v_a_3637_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3653_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3653_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3653_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
uint8_t v___x_3643_; 
v___x_3643_ = lean_unbox(v_a_3639_);
lean_dec(v_a_3639_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3645_; 
lean_dec(v_fst_3635_);
lean_del_object(v___x_3594_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3553_);
v___x_3645_ = v___x_3641_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3553_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
else
{
lean_object* v___x_3648_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 0, v_fst_3635_);
v___x_3648_ = v___x_3594_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_fst_3635_);
v___x_3648_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3650_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3648_);
v___x_3650_ = v___x_3641_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
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
}
else
{
lean_object* v_a_3654_; 
lean_dec(v_fst_3635_);
lean_del_object(v___x_3594_);
v_a_3654_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3638_, 1);
v_a_3437_ = v_a_3654_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3655_; 
lean_dec(v_fst_3635_);
lean_del_object(v___x_3594_);
lean_dec(v_a_3456_);
v_a_3655_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3636_, 1);
v_a_3437_ = v_a_3655_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3656_; 
lean_del_object(v___x_3594_);
lean_dec(v_a_3456_);
v_a_3656_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3633_, 1);
v_a_3437_ = v_a_3656_;
goto v___jp_3436_;
}
}
else
{
lean_object* v___x_3658_; 
lean_dec(v_a_3615_);
lean_del_object(v___x_3594_);
lean_dec(v_val_3592_);
lean_dec_ref_known(v___x_3569_, 2);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 0, v___x_3553_);
v___x_3658_ = v___x_3617_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3553_);
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
lean_object* v_a_3661_; 
lean_del_object(v___x_3594_);
lean_dec(v_val_3592_);
lean_dec_ref_known(v___x_3569_, 2);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3661_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3614_, 1);
v_a_3437_ = v_a_3661_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3662_; 
lean_dec(v_a_3597_);
lean_del_object(v___x_3594_);
lean_dec(v_val_3592_);
lean_dec_ref_known(v___x_3569_, 2);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3662_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3598_, 1);
v_a_3437_ = v_a_3662_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3663_; 
lean_del_object(v___x_3594_);
lean_dec(v_val_3592_);
lean_dec_ref_known(v___x_3569_, 2);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3663_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3596_, 1);
v_a_3437_ = v_a_3663_;
goto v___jp_3436_;
}
}
}
else
{
lean_object* v___x_3666_; 
lean_dec(v_a_3588_);
lean_dec_ref_known(v___x_3569_, 2);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v___x_3553_);
v___x_3666_ = v___x_3590_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3553_);
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
lean_object* v_a_3669_; 
lean_dec_ref_known(v___x_3569_, 2);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3669_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3669_);
lean_dec_ref_known(v___x_3587_, 1);
v_a_3437_ = v_a_3669_;
goto v___jp_3436_;
}
}
else
{
lean_object* v___x_3671_; 
lean_dec_ref_known(v___x_3569_, 2);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3578_);
v___x_3671_ = v___x_3488_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3578_);
v___x_3671_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3673_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3671_);
v___x_3673_ = v___x_3584_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
else
{
lean_object* v_a_3677_; 
lean_dec_ref(v___x_3578_);
lean_dec_ref_known(v___x_3569_, 2);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3677_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3581_, 1);
v_a_3437_ = v_a_3677_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3678_; 
lean_dec_ref(v___x_3578_);
lean_dec_ref_known(v___x_3569_, 2);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3678_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3579_, 1);
v_a_3437_ = v_a_3678_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3679_; 
lean_dec(v_a_3563_);
lean_dec(v_a_3561_);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3679_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3564_, 1);
v_a_3437_ = v_a_3679_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3680_; 
lean_dec(v_a_3561_);
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3680_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v___x_3562_, 1);
v_a_3437_ = v_a_3680_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3681_; 
lean_dec(v_a_3559_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3681_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3560_, 1);
v_a_3437_ = v_a_3681_;
goto v___jp_3436_;
}
}
else
{
lean_object* v___x_3683_; 
lean_dec(v_a_3555_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3553_);
v___x_3683_ = v___x_3557_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3553_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_a_3686_; 
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3686_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3554_, 1);
v_a_3437_ = v_a_3686_;
goto v___jp_3436_;
}
}
}
}
else
{
lean_object* v_a_3689_; 
lean_dec(v_a_3537_);
lean_dec(v_a_3527_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3689_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v___x_3538_, 1);
v_a_3437_ = v_a_3689_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3690_; 
lean_dec(v_a_3527_);
lean_dec(v_u_3525_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3690_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3690_);
lean_dec_ref_known(v___x_3536_, 1);
v_a_3437_ = v_a_3690_;
goto v___jp_3436_;
}
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3693_; 
lean_dec(v_a_3527_);
lean_dec(v_u_3525_);
lean_dec(v_u_3517_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v___x_3691_ = lean_box(0);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3691_);
v___x_3693_ = v___x_3533_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
else
{
lean_object* v_a_3696_; 
lean_dec(v_a_3527_);
lean_dec(v_u_3525_);
lean_dec(v_u_3517_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3696_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3530_, 1);
v_a_3437_ = v_a_3696_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3697_; 
lean_dec(v_a_3527_);
lean_dec(v_u_3525_);
lean_dec(v_u_3517_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3697_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___x_3528_, 1);
v_a_3437_ = v_a_3697_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3698_; 
lean_dec(v_u_3525_);
lean_dec(v_u_3524_);
lean_dec(v_u_3517_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3698_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3698_);
lean_dec_ref_known(v___x_3526_, 1);
v_a_3437_ = v_a_3698_;
goto v___jp_3436_;
}
}
else
{
lean_object* v___x_3699_; 
lean_dec(v_u_3517_);
lean_dec(v_u_3516_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v___x_3699_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3521_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
lean_dec_ref_known(v_a_3521_, 3);
v___y_3445_ = v___x_3699_;
goto v___jp_3444_;
}
}
else
{
lean_object* v___x_3700_; 
lean_dec(v_u_3517_);
lean_dec(v_u_3516_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v___x_3700_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3521_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
lean_dec_ref_known(v_a_3521_, 3);
v___y_3445_ = v___x_3700_;
goto v___jp_3444_;
}
}
else
{
lean_object* v___x_3701_; 
lean_dec(v_u_3517_);
lean_dec(v_u_3516_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v___x_3701_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3521_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
lean_dec(v_a_3521_);
v___y_3445_ = v___x_3701_;
goto v___jp_3444_;
}
}
else
{
lean_object* v_a_3702_; 
lean_dec(v_u_3517_);
lean_dec(v_u_3516_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3702_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3702_);
lean_dec_ref_known(v___x_3520_, 1);
v_a_3437_ = v_a_3702_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3703_; 
lean_dec(v_u_3517_);
lean_dec(v_u_3516_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3703_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3703_);
lean_dec_ref_known(v___x_3518_, 1);
v_a_3437_ = v_a_3703_;
goto v___jp_3436_;
}
}
else
{
lean_object* v___x_3704_; 
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v___x_3704_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3513_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
lean_dec_ref_known(v_a_3513_, 3);
v___y_3445_ = v___x_3704_;
goto v___jp_3444_;
}
}
else
{
lean_object* v___x_3705_; 
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v___x_3705_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3513_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
lean_dec_ref_known(v_a_3513_, 3);
v___y_3445_ = v___x_3705_;
goto v___jp_3444_;
}
}
else
{
lean_object* v___x_3706_; 
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v___x_3706_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3513_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
lean_dec(v_a_3513_);
v___y_3445_ = v___x_3706_;
goto v___jp_3444_;
}
}
else
{
lean_object* v_a_3707_; 
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3707_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3512_, 1);
v_a_3437_ = v_a_3707_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_a_3708_; 
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3708_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3510_, 1);
v_a_3437_ = v_a_3708_;
goto v___jp_3436_;
}
}
}
else
{
lean_object* v___x_3709_; 
lean_del_object(v___x_3500_);
lean_del_object(v___x_3493_);
lean_del_object(v___x_3479_);
lean_dec(v_a_3463_);
lean_dec(v_a_3456_);
v___x_3709_ = l_Lean_Meta_isMonad_x3f(v_fst_3476_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3802_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3712_ = v___x_3709_;
v_isShared_3713_ = v_isSharedCheck_3802_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3709_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3802_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
if (lean_obj_tag(v_a_3710_) == 1)
{
lean_object* v___x_3714_; lean_object* v___x_3716_; 
v___x_3714_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v_fst_3490_);
v___x_3716_ = v___x_3488_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_fst_3490_);
v___x_3716_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3718_; 
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v_snd_3491_);
v___x_3718_ = v___x_3474_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_snd_3491_);
v___x_3718_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3720_; 
if (v_isShared_3466_ == 0)
{
lean_ctor_set_tag(v___x_3465_, 1);
lean_ctor_set(v___x_3465_, 0, v_snd_3477_);
v___x_3720_ = v___x_3465_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_snd_3477_);
v___x_3720_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; lean_object* v_a_3723_; lean_object* v___x_3750_; 
v___x_3721_ = lean_box(0);
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 1);
lean_ctor_set(v___x_3458_, 0, v_e_3429_);
v___x_3750_ = v___x_3458_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_e_3429_);
v___x_3750_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3749_;
}
v___jp_3722_:
{
uint8_t v___x_3724_; 
v___x_3724_ = l_Lean_Exception_isInterrupt(v_a_3723_);
if (v___x_3724_ == 0)
{
uint8_t v___x_3725_; 
lean_inc_ref(v_a_3723_);
v___x_3725_ = l_Lean_Exception_isRuntime(v_a_3723_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; 
lean_dec_ref(v_a_3723_);
lean_del_object(v___x_3712_);
v___x_3726_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3496_, v_a_3432_, v_a_3434_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3733_ == 0)
{
lean_object* v_unused_3734_; 
v_unused_3734_ = lean_ctor_get(v___x_3726_, 0);
lean_dec(v_unused_3734_);
v___x_3728_ = v___x_3726_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_dec(v___x_3726_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 0, v___x_3721_);
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3721_);
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
v_a_3735_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3726_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3726_);
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
else
{
lean_object* v___x_3744_; 
lean_dec(v_a_3496_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set_tag(v___x_3712_, 1);
lean_ctor_set(v___x_3712_, 0, v_a_3723_);
v___x_3744_ = v___x_3712_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3723_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
else
{
lean_object* v___x_3747_; 
lean_dec(v_a_3496_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set_tag(v___x_3712_, 1);
lean_ctor_set(v___x_3712_, 0, v_a_3723_);
v___x_3747_ = v___x_3712_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3723_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
v_reusejp_3749_:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3751_ = lean_unsigned_to_nat(6u);
v___x_3752_ = lean_mk_empty_array_with_capacity(v___x_3751_);
v___x_3753_ = lean_array_push(v___x_3752_, v___x_3716_);
v___x_3754_ = lean_array_push(v___x_3753_, v___x_3718_);
v___x_3755_ = lean_array_push(v___x_3754_, v___x_3720_);
v___x_3756_ = lean_array_push(v___x_3755_, v___x_3721_);
v___x_3757_ = lean_array_push(v___x_3756_, v_a_3710_);
v___x_3758_ = lean_array_push(v___x_3757_, v___x_3750_);
v___x_3759_ = l_Lean_Meta_mkAppOptM(v___x_3714_, v___x_3758_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3778_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3762_ = v___x_3759_;
v_isShared_3763_ = v_isSharedCheck_3778_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3759_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3778_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Meta_expandCoe(v_a_3760_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3776_; 
lean_del_object(v___x_3712_);
lean_dec(v_a_3496_);
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3767_ = v___x_3764_;
v_isShared_3768_ = v_isSharedCheck_3776_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3764_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3776_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v_fst_3769_; lean_object* v___x_3771_; 
v_fst_3769_ = lean_ctor_get(v_a_3765_, 0);
lean_inc(v_fst_3769_);
lean_dec(v_a_3765_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set_tag(v___x_3762_, 1);
lean_ctor_set(v___x_3762_, 0, v_fst_3769_);
v___x_3771_ = v___x_3762_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_fst_3769_);
v___x_3771_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3773_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v___x_3771_);
v___x_3773_ = v___x_3767_;
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
lean_object* v_a_3777_; 
lean_del_object(v___x_3762_);
v_a_3777_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3764_, 1);
v_a_3723_ = v_a_3777_;
goto v___jp_3722_;
}
}
}
else
{
lean_object* v_a_3779_; 
v_a_3779_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___x_3759_, 1);
v_a_3723_ = v_a_3779_;
goto v___jp_3722_;
}
}
}
}
}
}
else
{
lean_object* v___x_3784_; 
lean_del_object(v___x_3712_);
lean_dec(v_a_3710_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_dec(v_snd_3477_);
lean_del_object(v___x_3474_);
lean_del_object(v___x_3465_);
lean_del_object(v___x_3458_);
lean_dec_ref(v_e_3429_);
v___x_3784_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3496_, v_a_3432_, v_a_3434_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3792_; 
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3792_ == 0)
{
lean_object* v_unused_3793_; 
v_unused_3793_ = lean_ctor_get(v___x_3784_, 0);
lean_dec(v_unused_3793_);
v___x_3786_ = v___x_3784_;
v_isShared_3787_ = v_isSharedCheck_3792_;
goto v_resetjp_3785_;
}
else
{
lean_dec(v___x_3784_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3792_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3788_; lean_object* v___x_3790_; 
v___x_3788_ = lean_box(0);
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v___x_3788_);
v___x_3790_ = v___x_3786_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
v_a_3794_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3784_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3784_);
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
lean_dec(v_a_3496_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_dec(v_snd_3477_);
lean_del_object(v___x_3474_);
lean_del_object(v___x_3465_);
lean_del_object(v___x_3458_);
lean_dec_ref(v_e_3429_);
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_dec(v_a_3496_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_del_object(v___x_3474_);
lean_del_object(v___x_3465_);
lean_dec(v_a_3463_);
lean_del_object(v___x_3458_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3804_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3497_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3497_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_del_object(v___x_3474_);
lean_del_object(v___x_3465_);
lean_dec(v_a_3463_);
lean_del_object(v___x_3458_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3812_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3495_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3495_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3824_; 
lean_dec(v_a_3482_);
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_del_object(v___x_3474_);
lean_del_object(v___x_3465_);
lean_dec(v_a_3463_);
lean_del_object(v___x_3458_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v___x_3822_ = lean_box(0);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3822_);
v___x_3824_ = v___x_3484_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3822_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_del_object(v___x_3479_);
lean_dec(v_snd_3477_);
lean_dec(v_fst_3476_);
lean_del_object(v___x_3474_);
lean_del_object(v___x_3465_);
lean_dec(v_a_3463_);
lean_del_object(v___x_3458_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3827_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3481_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3481_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
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
}
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3839_; 
lean_dec(v_a_3468_);
lean_del_object(v___x_3465_);
lean_dec(v_a_3463_);
lean_del_object(v___x_3458_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v___x_3837_ = lean_box(0);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3837_);
v___x_3839_ = v___x_3470_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_del_object(v___x_3465_);
lean_dec(v_a_3463_);
lean_del_object(v___x_3458_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3842_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3467_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3467_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_del_object(v___x_3458_);
lean_dec(v_a_3456_);
lean_dec_ref(v_e_3429_);
v_a_3851_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3460_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3460_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3860_, lean_object* v_expectedType_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3860_, v_expectedType_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3868_, lean_object* v_expectedType_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v___x_3875_; 
lean_inc_ref(v_expectedType_3869_);
lean_inc_ref(v_expr_3868_);
v___x_3875_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3868_, v_expectedType_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3955_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3878_ = v___x_3875_;
v_isShared_3879_ = v_isSharedCheck_3955_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3875_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3955_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
if (lean_obj_tag(v_a_3876_) == 1)
{
lean_object* v_val_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3892_; 
lean_dec_ref(v_expectedType_3869_);
lean_dec_ref(v_expr_3868_);
v_val_3880_ = lean_ctor_get(v_a_3876_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_a_3876_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3882_ = v_a_3876_;
v_isShared_3883_ = v_isSharedCheck_3892_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_val_3880_);
lean_dec(v_a_3876_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3892_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3884_ = lean_box(0);
v___x_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3885_, 0, v_val_3880_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v___x_3885_);
v___x_3887_ = v___x_3882_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3889_; 
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 0, v___x_3887_);
v___x_3889_ = v___x_3878_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
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
else
{
lean_object* v___x_3893_; 
lean_del_object(v___x_3878_);
lean_dec(v_a_3876_);
lean_inc_ref(v_expectedType_3869_);
v___x_3893_ = l_Lean_Meta_whnfR(v_expectedType_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; uint8_t v___x_3895_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v___x_3895_ = l_Lean_Expr_isForall(v_a_3894_);
lean_dec(v_a_3894_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3868_, v_expectedType_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
return v___x_3896_;
}
else
{
lean_object* v___x_3897_; 
lean_inc_ref(v_expr_3868_);
v___x_3897_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3868_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
if (lean_obj_tag(v_a_3898_) == 1)
{
lean_object* v_val_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3937_; 
v_val_3899_ = lean_ctor_get(v_a_3898_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_a_3898_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3901_ = v_a_3898_;
v_isShared_3902_ = v_isSharedCheck_3937_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_val_3899_);
lean_dec(v_a_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3937_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; 
lean_inc(v_a_3873_);
lean_inc_ref(v_a_3872_);
lean_inc(v_a_3871_);
lean_inc_ref(v_a_3870_);
lean_inc(v_val_3899_);
v___x_3903_ = lean_infer_type(v_val_3899_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3905_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
lean_inc_ref(v_expectedType_3869_);
v___x_3905_ = l_Lean_Meta_isExprDefEq(v_a_3904_, v_expectedType_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3920_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_3920_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3920_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
uint8_t v___x_3910_; 
v___x_3910_ = lean_unbox(v_a_3906_);
lean_dec(v_a_3906_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; 
lean_del_object(v___x_3908_);
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
v___x_3911_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3868_, v_expectedType_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
return v___x_3911_;
}
else
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec_ref(v_expectedType_3869_);
lean_dec_ref(v_expr_3868_);
v___x_3912_ = lean_box(0);
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v_val_3899_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3913_);
v___x_3915_ = v___x_3901_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3917_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3915_);
v___x_3917_ = v___x_3908_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_dec_ref(v_expectedType_3869_);
lean_dec_ref(v_expr_3868_);
v_a_3921_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3905_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3905_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_dec_ref(v_expectedType_3869_);
lean_dec_ref(v_expr_3868_);
v_a_3929_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3903_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3903_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
}
else
{
lean_object* v___x_3938_; 
lean_dec(v_a_3898_);
v___x_3938_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3868_, v_expectedType_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
return v___x_3938_;
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_dec_ref(v_expectedType_3869_);
lean_dec_ref(v_expr_3868_);
v_a_3939_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3897_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3897_);
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
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v_expectedType_3869_);
lean_dec_ref(v_expr_3868_);
v_a_3947_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3893_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3893_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec_ref(v_expectedType_3869_);
lean_dec_ref(v_expr_3868_);
v_a_3956_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3875_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3875_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3964_, lean_object* v_expectedType_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3964_, v_expectedType_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
lean_dec(v_a_3969_);
lean_dec_ref(v_a_3968_);
lean_dec(v_a_3967_);
lean_dec_ref(v_a_3966_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3972_, lean_object* v_expectedType_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3972_, v_expectedType_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4004_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3982_ = v___x_3979_;
v_isShared_3983_ = v_isSharedCheck_4004_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3979_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4004_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
switch(lean_obj_tag(v_a_3980_))
{
case 0:
{
lean_object* v___x_3984_; lean_object* v___x_3986_; 
v___x_3984_ = lean_box(0);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_3984_);
v___x_3986_ = v___x_3982_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
case 1:
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3999_; 
v_a_3988_ = lean_ctor_get(v_a_3980_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_a_3980_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3990_ = v_a_3980_;
v_isShared_3991_ = v_isSharedCheck_3999_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v_a_3980_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3999_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v_fst_3992_; lean_object* v___x_3994_; 
v_fst_3992_ = lean_ctor_get(v_a_3988_, 0);
lean_inc(v_fst_3992_);
lean_dec(v_a_3988_);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 0, v_fst_3992_);
v___x_3994_ = v___x_3990_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_fst_3992_);
v___x_3994_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3996_; 
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_3994_);
v___x_3996_ = v___x_3982_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
default: 
{
lean_object* v___x_4000_; lean_object* v___x_4002_; 
v___x_4000_ = lean_box(2);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_4000_);
v___x_4002_ = v___x_3982_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
v_a_4005_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3979_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3979_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_4013_, lean_object* v_expectedType_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_Meta_coerce_x3f(v_expr_4013_, v_expectedType_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
return v_res_4020_;
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
