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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
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
size_t v_x_38382__boxed_320_; uint8_t v_res_321_; lean_object* v_r_322_; 
v_x_38382__boxed_320_ = lean_unbox_usize(v_x_318_);
lean_dec(v_x_318_);
v_res_321_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_317_, v_x_38382__boxed_320_, v_x_319_);
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
v___x_338_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
lean_ctor_set(v___x_338_, 3, v___x_337_);
lean_ctor_set(v___x_338_, 4, v___x_337_);
lean_ctor_set(v___x_338_, 5, v___x_337_);
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
v___y_377_ = v___y_431_;
v___y_378_ = v_auxDeclNGen_438_;
v___y_379_ = v_messages_441_;
v___y_380_ = v___y_430_;
v___y_381_ = v_traceState_439_;
v___y_382_ = v_snapshotTasks_443_;
v___y_383_ = v_ngen_437_;
v___y_384_ = v_nextMacroScope_436_;
v___y_385_ = v_infoState_442_;
v___y_386_ = v___y_429_;
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
v___y_377_ = v___y_431_;
v___y_378_ = v_auxDeclNGen_449_;
v___y_379_ = v_messages_452_;
v___y_380_ = v___y_430_;
v___y_381_ = v_traceState_450_;
v___y_382_ = v_snapshotTasks_454_;
v___y_383_ = v_ngen_448_;
v___y_384_ = v_nextMacroScope_447_;
v___y_385_ = v_infoState_453_;
v___y_386_ = v___y_429_;
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
lean_ctor_set(v___x_390_, 1, v___y_384_);
lean_ctor_set(v___x_390_, 2, v___y_383_);
lean_ctor_set(v___x_390_, 3, v___y_378_);
lean_ctor_set(v___x_390_, 4, v___y_381_);
lean_ctor_set(v___x_390_, 5, v___x_389_);
lean_ctor_set(v___x_390_, 6, v___y_387_);
lean_ctor_set(v___x_390_, 7, v___y_379_);
lean_ctor_set(v___x_390_, 8, v___y_385_);
lean_ctor_set(v___x_390_, 9, v___y_382_);
v___x_391_ = lean_st_ref_put(v___y_377_, v___x_390_);
v___x_392_ = lean_st_ref_take(v___y_380_);
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
v___x_404_ = lean_st_ref_put(v___y_380_, v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_400_);
lean_ctor_set(v___x_405_, 1, v___y_386_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(lean_object* v___x_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed(lean_object* v___x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(v___x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
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
lean_object* v___y_1069_; lean_object* v_toCold_1086_; lean_object* v_currRecDepth_1087_; lean_object* v_ref_1088_; uint16_t v_optionFlags_1089_; uint8_t v_suppressElabErrors_1090_; uint8_t v_isRecordingDeps_1091_; lean_object* v_maxRecDepth_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_toCold_1086_ = lean_ctor_get(v___y_1065_, 0);
v_currRecDepth_1087_ = lean_ctor_get(v___y_1065_, 1);
v_ref_1088_ = lean_ctor_get(v___y_1065_, 2);
v_optionFlags_1089_ = lean_ctor_get_uint16(v___y_1065_, sizeof(void*)*3);
v_suppressElabErrors_1090_ = lean_ctor_get_uint8(v___y_1065_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1091_ = lean_ctor_get_uint8(v___y_1065_, sizeof(void*)*3 + 3);
v_maxRecDepth_1097_ = lean_ctor_get(v_toCold_1086_, 3);
v___x_1098_ = lean_unsigned_to_nat(0u);
v___x_1099_ = lean_nat_dec_eq(v_maxRecDepth_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_nat_dec_eq(v_currRecDepth_1087_, v_maxRecDepth_1097_);
if (v___x_1100_ == 0)
{
goto v___jp_1092_;
}
else
{
lean_object* v___x_1101_; 
lean_dec(v___y_1062_);
lean_dec_ref(v_x_1060_);
lean_inc(v_ref_1088_);
v___x_1101_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1088_);
v___y_1069_ = v___x_1101_;
goto v___jp_1068_;
}
}
else
{
goto v___jp_1092_;
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
v___jp_1092_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_currRecDepth_1087_, v___x_1093_);
lean_inc(v_ref_1088_);
lean_inc_ref(v_toCold_1086_);
v___x_1095_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1095_, 0, v_toCold_1086_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
lean_ctor_set(v___x_1095_, 2, v_ref_1088_);
lean_ctor_set_uint16(v___x_1095_, sizeof(void*)*3, v_optionFlags_1089_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*3 + 2, v_suppressElabErrors_1090_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*3 + 3, v_isRecordingDeps_1091_);
lean_inc(v___y_1066_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1061_);
v___x_1096_ = lean_apply_7(v_x_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___x_1095_, v___y_1066_, lean_box(0));
v___y_1069_ = v___x_1096_;
goto v___jp_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1103_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11___redArg(lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_box(0);
return v___x_1113_;
}
else
{
lean_object* v_key_1114_; lean_object* v_value_1115_; lean_object* v_tail_1116_; uint8_t v___x_1117_; 
v_key_1114_ = lean_ctor_get(v_x_1112_, 0);
v_value_1115_ = lean_ctor_get(v_x_1112_, 1);
v_tail_1116_ = lean_ctor_get(v_x_1112_, 2);
v___x_1117_ = l_Lean_ExprStructEq_beq(v_key_1114_, v_a_1111_);
if (v___x_1117_ == 0)
{
v_x_1112_ = v_tail_1116_;
goto _start;
}
else
{
lean_object* v___x_1119_; 
lean_inc(v_value_1115_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_value_1115_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11___redArg___boxed(lean_object* v_a_1120_, lean_object* v_x_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11___redArg(v_a_1120_, v_x_1121_);
lean_dec(v_x_1121_);
lean_dec_ref(v_a_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___redArg(lean_object* v_m_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_buckets_1125_; lean_object* v___x_1126_; uint64_t v___x_1127_; uint64_t v___x_1128_; uint64_t v___x_1129_; uint64_t v_fold_1130_; uint64_t v___x_1131_; uint64_t v___x_1132_; uint64_t v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_buckets_1125_ = lean_ctor_get(v_m_1123_, 1);
v___x_1126_ = lean_array_get_size(v_buckets_1125_);
v___x_1127_ = l_Lean_ExprStructEq_hash(v_a_1124_);
v___x_1128_ = 32ULL;
v___x_1129_ = lean_uint64_shift_right(v___x_1127_, v___x_1128_);
v_fold_1130_ = lean_uint64_xor(v___x_1127_, v___x_1129_);
v___x_1131_ = 16ULL;
v___x_1132_ = lean_uint64_shift_right(v_fold_1130_, v___x_1131_);
v___x_1133_ = lean_uint64_xor(v_fold_1130_, v___x_1132_);
v___x_1134_ = lean_uint64_to_usize(v___x_1133_);
v___x_1135_ = lean_usize_of_nat(v___x_1126_);
v___x_1136_ = ((size_t)1ULL);
v___x_1137_ = lean_usize_sub(v___x_1135_, v___x_1136_);
v___x_1138_ = lean_usize_land(v___x_1134_, v___x_1137_);
v___x_1139_ = lean_array_uget_borrowed(v_buckets_1125_, v___x_1138_);
v___x_1140_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11___redArg(v_a_1124_, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_m_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___redArg(v_m_1141_, v_a_1142_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_m_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1144_, lean_object* v_x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_apply_1(v_x_1145_, lean_box(0));
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v___y_1146_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1155_, v_x_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1164_, lean_object* v_pre_1165_, lean_object* v_post_1166_, lean_object* v_usedLetOnly_1167_, lean_object* v_skipConstInApp_1168_, lean_object* v_skipInstances_1169_, lean_object* v_postApp_1170_, lean_object* v_body_1171_, lean_object* v_x_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v_usedLetOnly_boxed_1180_; uint8_t v_skipConstInApp_boxed_1181_; uint8_t v_skipInstances_boxed_1182_; lean_object* v_res_1183_; 
v_usedLetOnly_boxed_1180_ = lean_unbox(v_usedLetOnly_1167_);
v_skipConstInApp_boxed_1181_ = lean_unbox(v_skipConstInApp_1168_);
v_skipInstances_boxed_1182_ = lean_unbox(v_skipInstances_1169_);
v_res_1183_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1164_, v_pre_1165_, v_post_1166_, v_usedLetOnly_boxed_1180_, v_skipConstInApp_boxed_1181_, v_skipInstances_boxed_1182_, v_postApp_1170_, v_body_1171_, v_x_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1173_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1187_, lean_object* v_pre_1188_, lean_object* v_post_1189_, uint8_t v_usedLetOnly_1190_, uint8_t v_skipConstInApp_1191_, uint8_t v_skipInstances_1192_, lean_object* v_postApp_1193_, lean_object* v_body_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_array_push(v_fvars_1187_, v_x_1195_);
v___x_1204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1188_, v_post_1189_, v_usedLetOnly_1190_, v_skipConstInApp_1191_, v_skipInstances_1192_, v_postApp_1193_, v___x_1203_, v_body_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1205_, lean_object* v_pre_1206_, lean_object* v_post_1207_, lean_object* v_usedLetOnly_1208_, lean_object* v_skipConstInApp_1209_, lean_object* v_skipInstances_1210_, lean_object* v_postApp_1211_, lean_object* v_body_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
uint8_t v_usedLetOnly_boxed_1221_; uint8_t v_skipConstInApp_boxed_1222_; uint8_t v_skipInstances_boxed_1223_; lean_object* v_res_1224_; 
v_usedLetOnly_boxed_1221_ = lean_unbox(v_usedLetOnly_1208_);
v_skipConstInApp_boxed_1222_ = lean_unbox(v_skipConstInApp_1209_);
v_skipInstances_boxed_1223_ = lean_unbox(v_skipInstances_1210_);
v_res_1224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1205_, v_pre_1206_, v_post_1207_, v_usedLetOnly_boxed_1221_, v_skipConstInApp_boxed_1222_, v_skipInstances_boxed_1223_, v_postApp_1211_, v_body_1212_, v_x_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1214_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_pre_1225_, lean_object* v_post_1226_, uint8_t v_usedLetOnly_1227_, uint8_t v_skipConstInApp_1228_, uint8_t v_skipInstances_1229_, lean_object* v_postApp_1230_, lean_object* v_e_1231_, lean_object* v_a_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
lean_inc_ref(v_post_1226_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
lean_inc_ref(v_e_1231_);
v___x_1239_ = lean_apply_7(v_post_1226_, v_e_1231_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, lean_box(0));
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1271_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1271_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1271_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1270_; 
v_fst_1244_ = lean_ctor_get(v_a_1240_, 0);
v_snd_1245_ = lean_ctor_get(v_a_1240_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_a_1240_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1247_ = v_a_1240_;
v_isShared_1248_ = v_isSharedCheck_1270_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_snd_1245_);
lean_inc(v_fst_1244_);
lean_dec(v_a_1240_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1270_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___y_1250_; 
switch(lean_obj_tag(v_fst_1244_))
{
case 0:
{
lean_object* v_e_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1265_; 
lean_del_object(v___x_1247_);
lean_del_object(v___x_1242_);
lean_dec_ref(v_e_1231_);
lean_dec_ref(v_postApp_1230_);
lean_dec_ref(v_post_1226_);
lean_dec_ref(v_pre_1225_);
v_e_1257_ = lean_ctor_get(v_fst_1244_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_fst_1244_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1259_ = v_fst_1244_;
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_e_1257_);
lean_dec(v_fst_1244_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v_e_1257_);
lean_ctor_set(v___x_1261_, 1, v_snd_1245_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
case 1:
{
lean_object* v_e_1266_; lean_object* v___x_1267_; 
lean_del_object(v___x_1247_);
lean_del_object(v___x_1242_);
lean_dec_ref(v_e_1231_);
v_e_1266_ = lean_ctor_get(v_fst_1244_, 0);
lean_inc_ref(v_e_1266_);
lean_dec_ref_known(v_fst_1244_, 1);
v___x_1267_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1225_, v_post_1226_, v_usedLetOnly_1227_, v_skipConstInApp_1228_, v_skipInstances_1229_, v_postApp_1230_, v_e_1266_, v_a_1232_, v_snd_1245_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1267_;
}
default: 
{
lean_object* v_e_x3f_1268_; 
lean_dec_ref(v_postApp_1230_);
lean_dec_ref(v_post_1226_);
lean_dec_ref(v_pre_1225_);
v_e_x3f_1268_ = lean_ctor_get(v_fst_1244_, 0);
lean_inc(v_e_x3f_1268_);
lean_dec_ref_known(v_fst_1244_, 1);
if (lean_obj_tag(v_e_x3f_1268_) == 0)
{
v___y_1250_ = v_e_1231_;
goto v___jp_1249_;
}
else
{
lean_object* v_val_1269_; 
lean_dec_ref(v_e_1231_);
v_val_1269_ = lean_ctor_get(v_e_x3f_1268_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v_e_x3f_1268_, 1);
v___y_1250_ = v_val_1269_;
goto v___jp_1249_;
}
}
}
v___jp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___y_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___y_1250_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_snd_1245_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1254_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1252_);
v___x_1254_ = v___x_1242_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_e_1231_);
lean_dec_ref(v_postApp_1230_);
lean_dec_ref(v_post_1226_);
lean_dec_ref(v_pre_1225_);
v_a_1272_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1239_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1239_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1280_, lean_object* v_post_1281_, uint8_t v_usedLetOnly_1282_, uint8_t v_skipConstInApp_1283_, uint8_t v_skipInstances_1284_, lean_object* v_postApp_1285_, lean_object* v_fvars_1286_, lean_object* v_e_1287_, lean_object* v_a_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
if (lean_obj_tag(v_e_1287_) == 6)
{
lean_object* v_binderName_1295_; lean_object* v_binderType_1296_; lean_object* v_body_1297_; uint8_t v_binderInfo_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___f_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_binderName_1295_ = lean_ctor_get(v_e_1287_, 0);
lean_inc(v_binderName_1295_);
v_binderType_1296_ = lean_ctor_get(v_e_1287_, 1);
lean_inc_ref(v_binderType_1296_);
v_body_1297_ = lean_ctor_get(v_e_1287_, 2);
lean_inc_ref(v_body_1297_);
v_binderInfo_1298_ = lean_ctor_get_uint8(v_e_1287_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1287_, 3);
v___x_1299_ = lean_box(v_usedLetOnly_1282_);
v___x_1300_ = lean_box(v_skipConstInApp_1283_);
v___x_1301_ = lean_box(v_skipInstances_1284_);
lean_inc_ref(v_postApp_1285_);
lean_inc_ref(v_post_1281_);
lean_inc_ref(v_pre_1280_);
lean_inc_ref(v_fvars_1286_);
v___f_1302_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 16, 8);
lean_closure_set(v___f_1302_, 0, v_fvars_1286_);
lean_closure_set(v___f_1302_, 1, v_pre_1280_);
lean_closure_set(v___f_1302_, 2, v_post_1281_);
lean_closure_set(v___f_1302_, 3, v___x_1299_);
lean_closure_set(v___f_1302_, 4, v___x_1300_);
lean_closure_set(v___f_1302_, 5, v___x_1301_);
lean_closure_set(v___f_1302_, 6, v_postApp_1285_);
lean_closure_set(v___f_1302_, 7, v_body_1297_);
v___x_1303_ = lean_expr_instantiate_rev(v_binderType_1296_, v_fvars_1286_);
lean_dec_ref(v_fvars_1286_);
lean_dec_ref(v_binderType_1296_);
v___x_1304_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1280_, v_post_1281_, v_usedLetOnly_1282_, v_skipConstInApp_1283_, v_skipInstances_1284_, v_postApp_1285_, v___x_1303_, v_a_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v_fst_1306_; lean_object* v_snd_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v_fst_1306_ = lean_ctor_get(v_a_1305_, 0);
lean_inc(v_fst_1306_);
v_snd_1307_ = lean_ctor_get(v_a_1305_, 1);
lean_inc(v_snd_1307_);
lean_dec(v_a_1305_);
v___x_1308_ = 0;
v___x_1309_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1295_, v_binderInfo_1298_, v_fst_1306_, v___f_1302_, v___x_1308_, v_a_1288_, v_snd_1307_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1309_;
}
else
{
lean_dec_ref(v___f_1302_);
lean_dec(v_binderName_1295_);
return v___x_1304_;
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_expr_instantiate_rev(v_e_1287_, v_fvars_1286_);
lean_dec_ref(v_e_1287_);
lean_inc_ref(v_postApp_1285_);
lean_inc_ref(v_post_1281_);
lean_inc_ref(v_pre_1280_);
v___x_1311_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1280_, v_post_1281_, v_usedLetOnly_1282_, v_skipConstInApp_1283_, v_skipInstances_1284_, v_postApp_1285_, v___x_1310_, v_a_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v_fst_1313_; lean_object* v_snd_1314_; uint8_t v___x_1315_; uint8_t v___x_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v_fst_1313_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_fst_1313_);
v_snd_1314_ = lean_ctor_get(v_a_1312_, 1);
lean_inc(v_snd_1314_);
lean_dec(v_a_1312_);
v___x_1315_ = 0;
v___x_1316_ = 1;
v___x_1317_ = 1;
v___x_1318_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1286_, v_fst_1313_, v___x_1315_, v_usedLetOnly_1282_, v___x_1315_, v___x_1316_, v___x_1317_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec_ref(v_fvars_1286_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1280_, v_post_1281_, v_usedLetOnly_1282_, v_skipConstInApp_1283_, v_skipInstances_1284_, v_postApp_1285_, v_a_1319_, v_a_1288_, v_snd_1314_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1320_;
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v_snd_1314_);
lean_dec_ref(v_postApp_1285_);
lean_dec_ref(v_post_1281_);
lean_dec_ref(v_pre_1280_);
v_a_1321_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1318_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1318_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1286_);
lean_dec_ref(v_postApp_1285_);
lean_dec_ref(v_post_1281_);
lean_dec_ref(v_pre_1280_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1329_, lean_object* v_pre_1330_, lean_object* v_post_1331_, uint8_t v_usedLetOnly_1332_, uint8_t v_skipConstInApp_1333_, uint8_t v_skipInstances_1334_, lean_object* v_postApp_1335_, lean_object* v_body_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_array_push(v_fvars_1329_, v_x_1337_);
v___x_1346_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1330_, v_post_1331_, v_usedLetOnly_1332_, v_skipConstInApp_1333_, v_skipInstances_1334_, v_postApp_1335_, v___x_1345_, v_body_1336_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1347_, lean_object* v_pre_1348_, lean_object* v_post_1349_, lean_object* v_usedLetOnly_1350_, lean_object* v_skipConstInApp_1351_, lean_object* v_skipInstances_1352_, lean_object* v_postApp_1353_, lean_object* v_body_1354_, lean_object* v_x_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
uint8_t v_usedLetOnly_boxed_1363_; uint8_t v_skipConstInApp_boxed_1364_; uint8_t v_skipInstances_boxed_1365_; lean_object* v_res_1366_; 
v_usedLetOnly_boxed_1363_ = lean_unbox(v_usedLetOnly_1350_);
v_skipConstInApp_boxed_1364_ = lean_unbox(v_skipConstInApp_1351_);
v_skipInstances_boxed_1365_ = lean_unbox(v_skipInstances_1352_);
v_res_1366_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1347_, v_pre_1348_, v_post_1349_, v_usedLetOnly_boxed_1363_, v_skipConstInApp_boxed_1364_, v_skipInstances_boxed_1365_, v_postApp_1353_, v_body_1354_, v_x_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1356_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1367_, lean_object* v_post_1368_, uint8_t v_usedLetOnly_1369_, uint8_t v_skipConstInApp_1370_, uint8_t v_skipInstances_1371_, lean_object* v_postApp_1372_, lean_object* v_fvars_1373_, lean_object* v_e_1374_, lean_object* v_a_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
if (lean_obj_tag(v_e_1374_) == 8)
{
lean_object* v_declName_1382_; lean_object* v_type_1383_; lean_object* v_value_1384_; lean_object* v_body_1385_; uint8_t v_nondep_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_declName_1382_ = lean_ctor_get(v_e_1374_, 0);
lean_inc(v_declName_1382_);
v_type_1383_ = lean_ctor_get(v_e_1374_, 1);
lean_inc_ref(v_type_1383_);
v_value_1384_ = lean_ctor_get(v_e_1374_, 2);
lean_inc_ref(v_value_1384_);
v_body_1385_ = lean_ctor_get(v_e_1374_, 3);
lean_inc_ref(v_body_1385_);
v_nondep_1386_ = lean_ctor_get_uint8(v_e_1374_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1374_, 4);
v___x_1387_ = lean_box(v_usedLetOnly_1369_);
v___x_1388_ = lean_box(v_skipConstInApp_1370_);
v___x_1389_ = lean_box(v_skipInstances_1371_);
lean_inc_ref_n(v_postApp_1372_, 2);
lean_inc_ref_n(v_post_1368_, 2);
lean_inc_ref_n(v_pre_1367_, 2);
lean_inc_ref(v_fvars_1373_);
v___f_1390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 16, 8);
lean_closure_set(v___f_1390_, 0, v_fvars_1373_);
lean_closure_set(v___f_1390_, 1, v_pre_1367_);
lean_closure_set(v___f_1390_, 2, v_post_1368_);
lean_closure_set(v___f_1390_, 3, v___x_1387_);
lean_closure_set(v___f_1390_, 4, v___x_1388_);
lean_closure_set(v___f_1390_, 5, v___x_1389_);
lean_closure_set(v___f_1390_, 6, v_postApp_1372_);
lean_closure_set(v___f_1390_, 7, v_body_1385_);
v___x_1391_ = lean_expr_instantiate_rev(v_type_1383_, v_fvars_1373_);
lean_dec_ref(v_type_1383_);
v___x_1392_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1367_, v_post_1368_, v_usedLetOnly_1369_, v_skipConstInApp_1370_, v_skipInstances_1371_, v_postApp_1372_, v___x_1391_, v_a_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v_fst_1394_ = lean_ctor_get(v_a_1393_, 0);
lean_inc(v_fst_1394_);
v_snd_1395_ = lean_ctor_get(v_a_1393_, 1);
lean_inc(v_snd_1395_);
lean_dec(v_a_1393_);
v___x_1396_ = lean_expr_instantiate_rev(v_value_1384_, v_fvars_1373_);
lean_dec_ref(v_fvars_1373_);
lean_dec_ref(v_value_1384_);
v___x_1397_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1367_, v_post_1368_, v_usedLetOnly_1369_, v_skipConstInApp_1370_, v_skipInstances_1371_, v_postApp_1372_, v___x_1396_, v_a_1375_, v_snd_1395_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v_fst_1399_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_fst_1399_);
v_snd_1400_ = lean_ctor_get(v_a_1398_, 1);
lean_inc(v_snd_1400_);
lean_dec(v_a_1398_);
v___x_1401_ = 0;
v___x_1402_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1382_, v_fst_1394_, v_fst_1399_, v___f_1390_, v_nondep_1386_, v___x_1401_, v_a_1375_, v_snd_1400_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1402_;
}
else
{
lean_dec(v_fst_1394_);
lean_dec_ref(v___f_1390_);
lean_dec(v_declName_1382_);
return v___x_1397_;
}
}
else
{
lean_dec_ref(v___f_1390_);
lean_dec_ref(v_value_1384_);
lean_dec(v_declName_1382_);
lean_dec_ref(v_fvars_1373_);
lean_dec_ref(v_postApp_1372_);
lean_dec_ref(v_post_1368_);
lean_dec_ref(v_pre_1367_);
return v___x_1392_;
}
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_expr_instantiate_rev(v_e_1374_, v_fvars_1373_);
lean_dec_ref(v_e_1374_);
lean_inc_ref(v_postApp_1372_);
lean_inc_ref(v_post_1368_);
lean_inc_ref(v_pre_1367_);
v___x_1404_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1367_, v_post_1368_, v_usedLetOnly_1369_, v_skipConstInApp_1370_, v_skipInstances_1371_, v_postApp_1372_, v___x_1403_, v_a_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_fst_1406_; lean_object* v_snd_1407_; uint8_t v___x_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v_fst_1406_ = lean_ctor_get(v_a_1405_, 0);
lean_inc(v_fst_1406_);
v_snd_1407_ = lean_ctor_get(v_a_1405_, 1);
lean_inc(v_snd_1407_);
lean_dec(v_a_1405_);
v___x_1408_ = 0;
v___x_1409_ = 1;
v___x_1410_ = l_Lean_Meta_mkLetFVars(v_fvars_1373_, v_fst_1406_, v_usedLetOnly_1369_, v___x_1408_, v___x_1409_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec_ref(v_fvars_1373_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1412_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1367_, v_post_1368_, v_usedLetOnly_1369_, v_skipConstInApp_1370_, v_skipInstances_1371_, v_postApp_1372_, v_a_1411_, v_a_1375_, v_snd_1407_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1412_;
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_snd_1407_);
lean_dec_ref(v_postApp_1372_);
lean_dec_ref(v_post_1368_);
lean_dec_ref(v_pre_1367_);
v_a_1413_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1410_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1410_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1373_);
lean_dec_ref(v_postApp_1372_);
lean_dec_ref(v_post_1368_);
lean_dec_ref(v_pre_1367_);
return v___x_1404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1421_, lean_object* v_post_1422_, uint8_t v_usedLetOnly_1423_, uint8_t v_skipConstInApp_1424_, uint8_t v_skipInstances_1425_, lean_object* v_postApp_1426_, size_t v_sz_1427_, size_t v_i_1428_, lean_object* v_bs_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_usize_dec_lt(v_i_1428_, v_sz_1427_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref(v_postApp_1426_);
lean_dec_ref(v_post_1422_);
lean_dec_ref(v_pre_1421_);
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
lean_inc_ref(v_postApp_1426_);
lean_inc_ref(v_post_1422_);
lean_inc_ref(v_pre_1421_);
v___x_1443_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1421_, v_post_1422_, v_usedLetOnly_1423_, v_skipConstInApp_1424_, v_skipInstances_1425_, v_postApp_1426_, v_v_1440_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
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
lean_dec_ref(v_postApp_1426_);
lean_dec_ref(v_post_1422_);
lean_dec_ref(v_pre_1421_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(lean_object* v_pre_1459_, lean_object* v_post_1460_, uint8_t v_usedLetOnly_1461_, uint8_t v_skipConstInApp_1462_, uint8_t v_skipInstances_1463_, lean_object* v_postApp_1464_, lean_object* v___x_1465_, lean_object* v___y_1466_, lean_object* v_b_1467_, lean_object* v_a_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1459_, v_post_1460_, v_usedLetOnly_1461_, v_skipConstInApp_1462_, v_skipInstances_1463_, v_postApp_1464_, v___x_1465_, v___y_1466_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1494_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1494_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1494_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_fst_1480_; lean_object* v_snd_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1493_; 
v_fst_1480_ = lean_ctor_get(v_a_1476_, 0);
v_snd_1481_ = lean_ctor_get(v_a_1476_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_a_1476_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1483_ = v_a_1476_;
v_isShared_1484_ = v_isSharedCheck_1493_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_snd_1481_);
lean_inc(v_fst_1480_);
lean_dec(v_a_1476_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1493_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1485_ = lean_array_fset(v_b_1467_, v_a_1468_, v_fst_1480_);
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1486_);
v___x_1488_ = v___x_1483_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_snd_1481_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1488_);
v___x_1490_ = v___x_1478_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec_ref(v_b_1467_);
v_a_1495_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1475_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1475_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed(lean_object* v_pre_1503_, lean_object* v_post_1504_, lean_object* v_usedLetOnly_1505_, lean_object* v_skipConstInApp_1506_, lean_object* v_skipInstances_1507_, lean_object* v_postApp_1508_, lean_object* v___x_1509_, lean_object* v___y_1510_, lean_object* v_b_1511_, lean_object* v_a_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v_usedLetOnly_boxed_1519_; uint8_t v_skipConstInApp_boxed_1520_; uint8_t v_skipInstances_boxed_1521_; lean_object* v_res_1522_; 
v_usedLetOnly_boxed_1519_ = lean_unbox(v_usedLetOnly_1505_);
v_skipConstInApp_boxed_1520_ = lean_unbox(v_skipConstInApp_1506_);
v_skipInstances_boxed_1521_ = lean_unbox(v_skipInstances_1507_);
v_res_1522_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(v_pre_1503_, v_post_1504_, v_usedLetOnly_boxed_1519_, v_skipConstInApp_boxed_1520_, v_skipInstances_boxed_1521_, v_postApp_1508_, v___x_1509_, v___y_1510_, v_b_1511_, v_a_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v_a_1512_);
lean_dec(v___y_1510_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_1523_, lean_object* v___x_1524_, lean_object* v_pre_1525_, lean_object* v_post_1526_, uint8_t v_usedLetOnly_1527_, uint8_t v_skipConstInApp_1528_, uint8_t v_skipInstances_1529_, lean_object* v_postApp_1530_, lean_object* v_a_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___y_1541_; uint8_t v___x_1575_; 
v___x_1575_ = lean_nat_dec_lt(v_a_1531_, v_upperBound_1523_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec(v_a_1531_);
lean_dec_ref(v_postApp_1530_);
lean_dec_ref(v_post_1526_);
lean_dec_ref(v_pre_1525_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v_b_1532_);
lean_ctor_set(v___x_1576_, 1, v___y_1534_);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
return v___x_1577_;
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1578_ = lean_array_fget_borrowed(v_b_1532_, v_a_1531_);
v___x_1579_ = lean_array_get_size(v___x_1524_);
v___x_1580_ = lean_nat_dec_lt(v_a_1531_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___f_1584_; 
lean_inc(v___x_1578_);
v___x_1581_ = lean_box(v_usedLetOnly_1527_);
v___x_1582_ = lean_box(v_skipConstInApp_1528_);
v___x_1583_ = lean_box(v_skipInstances_1529_);
lean_inc(v_a_1531_);
lean_inc(v___y_1533_);
lean_inc_ref(v_postApp_1530_);
lean_inc_ref(v_post_1526_);
lean_inc_ref(v_pre_1525_);
v___f_1584_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1584_, 0, v_pre_1525_);
lean_closure_set(v___f_1584_, 1, v_post_1526_);
lean_closure_set(v___f_1584_, 2, v___x_1581_);
lean_closure_set(v___f_1584_, 3, v___x_1582_);
lean_closure_set(v___f_1584_, 4, v___x_1583_);
lean_closure_set(v___f_1584_, 5, v_postApp_1530_);
lean_closure_set(v___f_1584_, 6, v___x_1578_);
lean_closure_set(v___f_1584_, 7, v___y_1533_);
lean_closure_set(v___f_1584_, 8, v_b_1532_);
lean_closure_set(v___f_1584_, 9, v_a_1531_);
v___y_1541_ = v___f_1584_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1585_; uint8_t v_isInstance_1586_; 
v___x_1585_ = lean_array_fget_borrowed(v___x_1524_, v_a_1531_);
v_isInstance_1586_ = lean_ctor_get_uint8(v___x_1585_, sizeof(void*)*1 + 4);
if (v_isInstance_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___f_1590_; 
lean_inc(v___x_1578_);
v___x_1587_ = lean_box(v_usedLetOnly_1527_);
v___x_1588_ = lean_box(v_skipConstInApp_1528_);
v___x_1589_ = lean_box(v_skipInstances_1529_);
lean_inc(v_a_1531_);
lean_inc(v___y_1533_);
lean_inc_ref(v_postApp_1530_);
lean_inc_ref(v_post_1526_);
lean_inc_ref(v_pre_1525_);
v___f_1590_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1590_, 0, v_pre_1525_);
lean_closure_set(v___f_1590_, 1, v_post_1526_);
lean_closure_set(v___f_1590_, 2, v___x_1587_);
lean_closure_set(v___f_1590_, 3, v___x_1588_);
lean_closure_set(v___f_1590_, 4, v___x_1589_);
lean_closure_set(v___f_1590_, 5, v_postApp_1530_);
lean_closure_set(v___f_1590_, 6, v___x_1578_);
lean_closure_set(v___f_1590_, 7, v___y_1533_);
lean_closure_set(v___f_1590_, 8, v_b_1532_);
lean_closure_set(v___f_1590_, 9, v_a_1531_);
v___y_1541_ = v___f_1590_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1591_; lean_object* v___f_1592_; 
v___x_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_b_1532_);
v___f_1592_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1592_, 0, v___x_1591_);
v___y_1541_ = v___f_1592_;
goto v___jp_1540_;
}
}
}
v___jp_1540_:
{
lean_object* v___x_1542_; 
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
lean_inc(v___y_1536_);
lean_inc_ref(v___y_1535_);
v___x_1542_ = lean_apply_6(v___y_1541_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, lean_box(0));
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1566_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1566_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1566_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_fst_1547_; 
v_fst_1547_ = lean_ctor_get(v_a_1543_, 0);
lean_inc(v_fst_1547_);
if (lean_obj_tag(v_fst_1547_) == 0)
{
lean_object* v_snd_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_a_1531_);
lean_dec_ref(v_postApp_1530_);
lean_dec_ref(v_post_1526_);
lean_dec_ref(v_pre_1525_);
v_snd_1548_ = lean_ctor_get(v_a_1543_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_a_1543_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v_a_1543_, 0);
lean_dec(v_unused_1560_);
v___x_1550_ = v_a_1543_;
v_isShared_1551_ = v_isSharedCheck_1559_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_snd_1548_);
lean_dec(v_a_1543_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1559_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_a_1552_; lean_object* v___x_1554_; 
v_a_1552_ = lean_ctor_get(v_fst_1547_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v_fst_1547_, 1);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v_a_1552_);
v___x_1554_ = v___x_1550_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_snd_1548_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1554_);
v___x_1556_ = v___x_1545_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_snd_1561_; lean_object* v_a_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_del_object(v___x_1545_);
v_snd_1561_ = lean_ctor_get(v_a_1543_, 1);
lean_inc(v_snd_1561_);
lean_dec(v_a_1543_);
v_a_1562_ = lean_ctor_get(v_fst_1547_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v_fst_1547_, 1);
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_nat_add(v_a_1531_, v___x_1563_);
lean_dec(v_a_1531_);
v_a_1531_ = v___x_1564_;
v_b_1532_ = v_a_1562_;
v___y_1534_ = v_snd_1561_;
goto _start;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1531_);
lean_dec_ref(v_postApp_1530_);
lean_dec_ref(v_post_1526_);
lean_dec_ref(v_pre_1525_);
v_a_1567_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1542_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1542_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1593_, lean_object* v_pre_1594_, lean_object* v_post_1595_, uint8_t v_usedLetOnly_1596_, uint8_t v_skipConstInApp_1597_, lean_object* v_postApp_1598_, lean_object* v___y_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_f_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; 
if (lean_obj_tag(v_x_1600_) == 5)
{
lean_object* v_fn_1674_; lean_object* v_arg_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_fn_1674_ = lean_ctor_get(v_x_1600_, 0);
lean_inc_ref(v_fn_1674_);
v_arg_1675_ = lean_ctor_get(v_x_1600_, 1);
lean_inc_ref(v_arg_1675_);
lean_dec_ref_known(v_x_1600_, 2);
v___x_1676_ = lean_array_set(v_x_1601_, v_x_1602_, v_arg_1675_);
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_nat_sub(v_x_1602_, v___x_1677_);
lean_dec(v_x_1602_);
v_x_1600_ = v_fn_1674_;
v_x_1601_ = v___x_1676_;
v_x_1602_ = v___x_1678_;
goto _start;
}
else
{
lean_dec(v_x_1602_);
if (v_skipConstInApp_1597_ == 0)
{
goto v___jp_1669_;
}
else
{
uint8_t v___x_1680_; 
v___x_1680_ = l_Lean_Expr_isConst(v_x_1600_);
if (v___x_1680_ == 0)
{
goto v___jp_1669_;
}
else
{
v_f_1611_ = v_x_1600_;
v___y_1612_ = v___y_1603_;
v___y_1613_ = v___y_1604_;
v___y_1614_ = v___y_1605_;
v___y_1615_ = v___y_1606_;
v___y_1616_ = v___y_1607_;
v___y_1617_ = v___y_1608_;
goto v___jp_1610_;
}
}
}
v___jp_1610_:
{
if (v_skipInstances_1593_ == 0)
{
size_t v_sz_1618_; size_t v___x_1619_; lean_object* v___x_1620_; 
v_sz_1618_ = lean_array_size(v_x_1601_);
v___x_1619_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_1598_);
lean_inc_ref(v_post_1595_);
lean_inc_ref(v_pre_1594_);
v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1594_, v_post_1595_, v_usedLetOnly_1596_, v_skipConstInApp_1597_, v_skipInstances_1593_, v_postApp_1598_, v_sz_1618_, v___x_1619_, v_x_1601_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v_fst_1622_ = lean_ctor_get(v_a_1621_, 0);
lean_inc(v_fst_1622_);
v_snd_1623_ = lean_ctor_get(v_a_1621_, 1);
lean_inc(v_snd_1623_);
lean_dec(v_a_1621_);
v___x_1624_ = l_Lean_mkAppN(v_f_1611_, v_fst_1622_);
lean_dec(v_fst_1622_);
lean_inc_ref(v_postApp_1598_);
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
v___x_1625_ = lean_apply_8(v_postApp_1598_, v___y_1599_, v___x_1624_, v_snd_1623_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, lean_box(0));
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v_fst_1627_; lean_object* v_snd_1628_; lean_object* v___x_1629_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v_fst_1627_ = lean_ctor_get(v_a_1626_, 0);
lean_inc(v_fst_1627_);
v_snd_1628_ = lean_ctor_get(v_a_1626_, 1);
lean_inc(v_snd_1628_);
lean_dec(v_a_1626_);
v___x_1629_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1594_, v_post_1595_, v_usedLetOnly_1596_, v_skipConstInApp_1597_, v_skipInstances_1593_, v_postApp_1598_, v_fst_1627_, v___y_1612_, v_snd_1628_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1629_;
}
else
{
lean_dec_ref(v_postApp_1598_);
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
return v___x_1625_;
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_f_1611_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_postApp_1598_);
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
v_a_1630_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1620_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1620_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_array_get_size(v_x_1601_);
lean_inc_ref(v_f_1611_);
v___x_1639_ = l_Lean_Meta_getFunInfoNArgs(v_f_1611_, v___x_1638_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v_paramInfo_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v_paramInfo_1641_ = lean_ctor_get(v_a_1640_, 0);
lean_inc_ref(v_paramInfo_1641_);
lean_dec(v_a_1640_);
v___x_1642_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_1598_);
lean_inc_ref(v_post_1595_);
lean_inc_ref(v_pre_1594_);
v___x_1643_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v___x_1638_, v_paramInfo_1641_, v_pre_1594_, v_post_1595_, v_usedLetOnly_1596_, v_skipConstInApp_1597_, v_skipInstances_1593_, v_postApp_1598_, v___x_1642_, v_x_1601_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec_ref(v_paramInfo_1641_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v_fst_1645_; lean_object* v_snd_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v_fst_1645_ = lean_ctor_get(v_a_1644_, 0);
lean_inc(v_fst_1645_);
v_snd_1646_ = lean_ctor_get(v_a_1644_, 1);
lean_inc(v_snd_1646_);
lean_dec(v_a_1644_);
v___x_1647_ = l_Lean_mkAppN(v_f_1611_, v_fst_1645_);
lean_dec(v_fst_1645_);
lean_inc_ref(v_postApp_1598_);
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
v___x_1648_ = lean_apply_8(v_postApp_1598_, v___y_1599_, v___x_1647_, v_snd_1646_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, lean_box(0));
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v_fst_1650_; lean_object* v_snd_1651_; lean_object* v___x_1652_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v_fst_1650_ = lean_ctor_get(v_a_1649_, 0);
lean_inc(v_fst_1650_);
v_snd_1651_ = lean_ctor_get(v_a_1649_, 1);
lean_inc(v_snd_1651_);
lean_dec(v_a_1649_);
v___x_1652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1594_, v_post_1595_, v_usedLetOnly_1596_, v_skipConstInApp_1597_, v_skipInstances_1593_, v_postApp_1598_, v_fst_1650_, v___y_1612_, v_snd_1651_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1652_;
}
else
{
lean_dec_ref(v_postApp_1598_);
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
return v___x_1648_;
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v_f_1611_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_postApp_1598_);
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
v_a_1653_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1643_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1643_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v___y_1613_);
lean_dec_ref(v_f_1611_);
lean_dec_ref(v_x_1601_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_postApp_1598_);
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
v_a_1661_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1639_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1639_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
v___jp_1669_:
{
lean_object* v___x_1670_; 
lean_inc_ref(v_postApp_1598_);
lean_inc_ref(v_post_1595_);
lean_inc_ref(v_pre_1594_);
v___x_1670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1594_, v_post_1595_, v_usedLetOnly_1596_, v_skipConstInApp_1597_, v_skipInstances_1593_, v_postApp_1598_, v_x_1600_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v_fst_1672_; lean_object* v_snd_1673_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v_fst_1672_ = lean_ctor_get(v_a_1671_, 0);
lean_inc(v_fst_1672_);
v_snd_1673_ = lean_ctor_get(v_a_1671_, 1);
lean_inc(v_snd_1673_);
lean_dec(v_a_1671_);
v_f_1611_ = v_fst_1672_;
v___y_1612_ = v___y_1603_;
v___y_1613_ = v_snd_1673_;
v___y_1614_ = v___y_1605_;
v___y_1615_ = v___y_1606_;
v___y_1616_ = v___y_1607_;
v___y_1617_ = v___y_1608_;
goto v___jp_1610_;
}
else
{
lean_dec_ref(v_x_1601_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_postApp_1598_);
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1681_, lean_object* v_pre_1682_, lean_object* v_e_1683_, lean_object* v_post_1684_, uint8_t v_usedLetOnly_1685_, uint8_t v_skipConstInApp_1686_, uint8_t v_skipInstances_1687_, lean_object* v_postApp_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Core_checkSystem(v___x_1681_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v___x_1697_; 
lean_dec_ref_known(v___x_1696_, 1);
lean_inc_ref(v_pre_1682_);
lean_inc(v___y_1694_);
lean_inc_ref(v___y_1693_);
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
lean_inc_ref(v_e_1683_);
v___x_1697_ = lean_apply_7(v_pre_1682_, v_e_1683_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, lean_box(0));
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1759_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1759_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1759_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_fst_1702_; lean_object* v_snd_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1758_; 
v_fst_1702_ = lean_ctor_get(v_a_1698_, 0);
v_snd_1703_ = lean_ctor_get(v_a_1698_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_a_1698_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1705_ = v_a_1698_;
v_isShared_1706_ = v_isSharedCheck_1758_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_snd_1703_);
lean_inc(v_fst_1702_);
lean_dec(v_a_1698_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1758_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___y_1708_; 
switch(lean_obj_tag(v_fst_1702_))
{
case 0:
{
lean_object* v_e_1747_; lean_object* v___x_1749_; 
lean_dec_ref(v_postApp_1688_);
lean_dec_ref(v_post_1684_);
lean_dec_ref(v_e_1683_);
lean_dec_ref(v_pre_1682_);
v_e_1747_ = lean_ctor_get(v_fst_1702_, 0);
lean_inc_ref(v_e_1747_);
lean_dec_ref_known(v_fst_1702_, 1);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v_e_1747_);
v___x_1749_ = v___x_1705_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_e_1747_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_snd_1703_);
v___x_1749_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1749_);
v___x_1751_ = v___x_1700_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
case 1:
{
lean_object* v_e_1754_; lean_object* v___x_1755_; 
lean_del_object(v___x_1705_);
lean_del_object(v___x_1700_);
lean_dec_ref(v_e_1683_);
v_e_1754_ = lean_ctor_get(v_fst_1702_, 0);
lean_inc_ref(v_e_1754_);
lean_dec_ref_known(v_fst_1702_, 1);
v___x_1755_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v_e_1754_, v___y_1689_, v_snd_1703_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1755_;
}
default: 
{
lean_object* v_e_x3f_1756_; 
lean_del_object(v___x_1705_);
lean_del_object(v___x_1700_);
v_e_x3f_1756_ = lean_ctor_get(v_fst_1702_, 0);
lean_inc(v_e_x3f_1756_);
lean_dec_ref_known(v_fst_1702_, 1);
if (lean_obj_tag(v_e_x3f_1756_) == 0)
{
v___y_1708_ = v_e_1683_;
goto v___jp_1707_;
}
else
{
lean_object* v_val_1757_; 
lean_dec_ref(v_e_1683_);
v_val_1757_ = lean_ctor_get(v_e_x3f_1756_, 0);
lean_inc(v_val_1757_);
lean_dec_ref_known(v_e_x3f_1756_, 1);
v___y_1708_ = v_val_1757_;
goto v___jp_1707_;
}
}
}
v___jp_1707_:
{
switch(lean_obj_tag(v___y_1708_))
{
case 7:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v___x_1709_, v___y_1708_, v___y_1689_, v_snd_1703_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1710_;
}
case 6:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1712_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v___x_1711_, v___y_1708_, v___y_1689_, v_snd_1703_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1712_;
}
case 8:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1714_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v___x_1713_, v___y_1708_, v___y_1689_, v_snd_1703_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1714_;
}
case 5:
{
lean_object* v_dummy_1715_; lean_object* v_nargs_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_dummy_1715_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1716_ = l_Lean_Expr_getAppNumArgs(v___y_1708_);
lean_inc(v_nargs_1716_);
v___x_1717_ = lean_mk_array(v_nargs_1716_, v_dummy_1715_);
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = lean_nat_sub(v_nargs_1716_, v___x_1718_);
lean_dec(v_nargs_1716_);
lean_inc_ref(v___y_1708_);
v___x_1720_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1687_, v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_postApp_1688_, v___y_1708_, v___y_1708_, v___x_1717_, v___x_1719_, v___y_1689_, v_snd_1703_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1720_;
}
case 10:
{
lean_object* v_data_1721_; lean_object* v_expr_1722_; lean_object* v___x_1723_; 
v_data_1721_ = lean_ctor_get(v___y_1708_, 0);
v_expr_1722_ = lean_ctor_get(v___y_1708_, 1);
lean_inc_ref(v_expr_1722_);
lean_inc_ref(v_postApp_1688_);
lean_inc_ref(v_post_1684_);
lean_inc_ref(v_pre_1682_);
v___x_1723_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v_expr_1722_, v___y_1689_, v_snd_1703_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v_fst_1725_; lean_object* v_snd_1726_; size_t v___x_1727_; size_t v___x_1728_; uint8_t v___x_1729_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v_fst_1725_ = lean_ctor_get(v_a_1724_, 0);
lean_inc(v_fst_1725_);
v_snd_1726_ = lean_ctor_get(v_a_1724_, 1);
lean_inc(v_snd_1726_);
lean_dec(v_a_1724_);
v___x_1727_ = lean_ptr_addr(v_expr_1722_);
v___x_1728_ = lean_ptr_addr(v_fst_1725_);
v___x_1729_ = lean_usize_dec_eq(v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_inc(v_data_1721_);
lean_dec_ref_known(v___y_1708_, 2);
v___x_1730_ = l_Lean_Expr_mdata___override(v_data_1721_, v_fst_1725_);
v___x_1731_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v___x_1730_, v___y_1689_, v_snd_1726_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; 
lean_dec(v_fst_1725_);
v___x_1732_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v___y_1708_, v___y_1689_, v_snd_1726_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1732_;
}
}
else
{
lean_dec_ref_known(v___y_1708_, 2);
lean_dec_ref(v_postApp_1688_);
lean_dec_ref(v_post_1684_);
lean_dec_ref(v_pre_1682_);
return v___x_1723_;
}
}
case 11:
{
lean_object* v_typeName_1733_; lean_object* v_idx_1734_; lean_object* v_struct_1735_; lean_object* v___x_1736_; 
v_typeName_1733_ = lean_ctor_get(v___y_1708_, 0);
v_idx_1734_ = lean_ctor_get(v___y_1708_, 1);
v_struct_1735_ = lean_ctor_get(v___y_1708_, 2);
lean_inc_ref(v_struct_1735_);
lean_inc_ref(v_postApp_1688_);
lean_inc_ref(v_post_1684_);
lean_inc_ref(v_pre_1682_);
v___x_1736_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v_struct_1735_, v___y_1689_, v_snd_1703_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v_fst_1738_; lean_object* v_snd_1739_; size_t v___x_1740_; size_t v___x_1741_; uint8_t v___x_1742_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v_fst_1738_ = lean_ctor_get(v_a_1737_, 0);
lean_inc(v_fst_1738_);
v_snd_1739_ = lean_ctor_get(v_a_1737_, 1);
lean_inc(v_snd_1739_);
lean_dec(v_a_1737_);
v___x_1740_ = lean_ptr_addr(v_struct_1735_);
v___x_1741_ = lean_ptr_addr(v_fst_1738_);
v___x_1742_ = lean_usize_dec_eq(v___x_1740_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_inc(v_idx_1734_);
lean_inc(v_typeName_1733_);
lean_dec_ref_known(v___y_1708_, 3);
v___x_1743_ = l_Lean_Expr_proj___override(v_typeName_1733_, v_idx_1734_, v_fst_1738_);
v___x_1744_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v___x_1743_, v___y_1689_, v_snd_1739_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; 
lean_dec(v_fst_1738_);
v___x_1745_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v___y_1708_, v___y_1689_, v_snd_1739_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1745_;
}
}
else
{
lean_dec_ref_known(v___y_1708_, 3);
lean_dec_ref(v_postApp_1688_);
lean_dec_ref(v_post_1684_);
lean_dec_ref(v_pre_1682_);
return v___x_1736_;
}
}
default: 
{
lean_object* v___x_1746_; 
v___x_1746_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1682_, v_post_1684_, v_usedLetOnly_1685_, v_skipConstInApp_1686_, v_skipInstances_1687_, v_postApp_1688_, v___y_1708_, v___y_1689_, v_snd_1703_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1746_;
}
}
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v_postApp_1688_);
lean_dec_ref(v_post_1684_);
lean_dec_ref(v_e_1683_);
lean_dec_ref(v_pre_1682_);
v_a_1760_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1697_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1697_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
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
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v___y_1690_);
lean_dec_ref(v_postApp_1688_);
lean_dec_ref(v_post_1684_);
lean_dec_ref(v_e_1683_);
lean_dec_ref(v_pre_1682_);
v_a_1768_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1696_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1696_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1776_, lean_object* v_pre_1777_, lean_object* v_e_1778_, lean_object* v_post_1779_, lean_object* v_usedLetOnly_1780_, lean_object* v_skipConstInApp_1781_, lean_object* v_skipInstances_1782_, lean_object* v_postApp_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
uint8_t v_usedLetOnly_boxed_1791_; uint8_t v_skipConstInApp_boxed_1792_; uint8_t v_skipInstances_boxed_1793_; lean_object* v_res_1794_; 
v_usedLetOnly_boxed_1791_ = lean_unbox(v_usedLetOnly_1780_);
v_skipConstInApp_boxed_1792_ = lean_unbox(v_skipConstInApp_1781_);
v_skipInstances_boxed_1793_ = lean_unbox(v_skipInstances_1782_);
v_res_1794_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1776_, v_pre_1777_, v_e_1778_, v_post_1779_, v_usedLetOnly_boxed_1791_, v_skipConstInApp_boxed_1792_, v_skipInstances_boxed_1793_, v_postApp_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1784_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1795_, lean_object* v_post_1796_, uint8_t v_usedLetOnly_1797_, uint8_t v_skipConstInApp_1798_, uint8_t v_skipInstances_1799_, lean_object* v_postApp_1800_, lean_object* v_e_1801_, lean_object* v_a_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_inc(v_a_1802_);
v___x_1809_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1809_, 0, lean_box(0));
lean_closure_set(v___x_1809_, 1, lean_box(0));
lean_closure_set(v___x_1809_, 2, v_a_1802_);
v___x_1810_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1809_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1865_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1865_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1865_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v_fst_1815_; lean_object* v_snd_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1864_; 
v_fst_1815_ = lean_ctor_get(v_a_1811_, 0);
v_snd_1816_ = lean_ctor_get(v_a_1811_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_a_1811_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1818_ = v_a_1811_;
v_isShared_1819_ = v_isSharedCheck_1864_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_snd_1816_);
lean_inc(v_fst_1815_);
lean_dec(v_a_1811_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1864_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___redArg(v_fst_1815_, v_e_1801_);
lean_dec(v_fst_1815_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___f_1825_; lean_object* v___x_1826_; 
lean_del_object(v___x_1818_);
lean_del_object(v___x_1813_);
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1822_ = lean_box(v_usedLetOnly_1797_);
v___x_1823_ = lean_box(v_skipConstInApp_1798_);
v___x_1824_ = lean_box(v_skipInstances_1799_);
lean_inc_ref(v_e_1801_);
v___f_1825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1825_, 0, v___x_1821_);
lean_closure_set(v___f_1825_, 1, v_pre_1795_);
lean_closure_set(v___f_1825_, 2, v_e_1801_);
lean_closure_set(v___f_1825_, 3, v_post_1796_);
lean_closure_set(v___f_1825_, 4, v___x_1822_);
lean_closure_set(v___f_1825_, 5, v___x_1823_);
lean_closure_set(v___f_1825_, 6, v___x_1824_);
lean_closure_set(v___f_1825_, 7, v_postApp_1800_);
v___x_1826_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1825_, v_a_1802_, v_snd_1816_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v_fst_1828_; lean_object* v_snd_1829_; lean_object* v___f_1830_; lean_object* v___x_1831_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v_fst_1828_ = lean_ctor_get(v_a_1827_, 0);
lean_inc_n(v_fst_1828_, 2);
v_snd_1829_ = lean_ctor_get(v_a_1827_, 1);
lean_inc(v_snd_1829_);
lean_dec(v_a_1827_);
lean_inc(v_a_1802_);
v___f_1830_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1830_, 0, v_a_1802_);
lean_closure_set(v___f_1830_, 1, v_e_1801_);
lean_closure_set(v___f_1830_, 2, v_fst_1828_);
v___x_1831_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1830_, v_snd_1829_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1848_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1848_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1848_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v_snd_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1846_; 
v_snd_1836_ = lean_ctor_get(v_a_1832_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_a_1832_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; 
v_unused_1847_ = lean_ctor_get(v_a_1832_, 0);
lean_dec(v_unused_1847_);
v___x_1838_ = v_a_1832_;
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_snd_1836_);
lean_dec(v_a_1832_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v_fst_1828_);
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_fst_1828_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_snd_1836_);
v___x_1841_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1841_);
v___x_1843_ = v___x_1834_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_fst_1828_);
v_a_1849_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1831_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1831_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_dec_ref(v_e_1801_);
return v___x_1826_;
}
}
else
{
lean_object* v_val_1857_; lean_object* v___x_1859_; 
lean_dec_ref(v_e_1801_);
lean_dec_ref(v_postApp_1800_);
lean_dec_ref(v_post_1796_);
lean_dec_ref(v_pre_1795_);
v_val_1857_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_val_1857_);
lean_dec_ref_known(v___x_1820_, 1);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v_val_1857_);
v___x_1859_ = v___x_1818_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_val_1857_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_snd_1816_);
v___x_1859_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1861_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1859_);
v___x_1861_ = v___x_1813_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v_e_1801_);
lean_dec_ref(v_postApp_1800_);
lean_dec_ref(v_post_1796_);
lean_dec_ref(v_pre_1795_);
v_a_1866_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1810_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1810_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1874_, lean_object* v_post_1875_, uint8_t v_usedLetOnly_1876_, uint8_t v_skipConstInApp_1877_, uint8_t v_skipInstances_1878_, lean_object* v_postApp_1879_, lean_object* v_fvars_1880_, lean_object* v_e_1881_, lean_object* v_a_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
if (lean_obj_tag(v_e_1881_) == 7)
{
lean_object* v_binderName_1889_; lean_object* v_binderType_1890_; lean_object* v_body_1891_; uint8_t v_binderInfo_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___f_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_binderName_1889_ = lean_ctor_get(v_e_1881_, 0);
lean_inc(v_binderName_1889_);
v_binderType_1890_ = lean_ctor_get(v_e_1881_, 1);
lean_inc_ref(v_binderType_1890_);
v_body_1891_ = lean_ctor_get(v_e_1881_, 2);
lean_inc_ref(v_body_1891_);
v_binderInfo_1892_ = lean_ctor_get_uint8(v_e_1881_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1881_, 3);
v___x_1893_ = lean_box(v_usedLetOnly_1876_);
v___x_1894_ = lean_box(v_skipConstInApp_1877_);
v___x_1895_ = lean_box(v_skipInstances_1878_);
lean_inc_ref(v_postApp_1879_);
lean_inc_ref(v_post_1875_);
lean_inc_ref(v_pre_1874_);
lean_inc_ref(v_fvars_1880_);
v___f_1896_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 16, 8);
lean_closure_set(v___f_1896_, 0, v_fvars_1880_);
lean_closure_set(v___f_1896_, 1, v_pre_1874_);
lean_closure_set(v___f_1896_, 2, v_post_1875_);
lean_closure_set(v___f_1896_, 3, v___x_1893_);
lean_closure_set(v___f_1896_, 4, v___x_1894_);
lean_closure_set(v___f_1896_, 5, v___x_1895_);
lean_closure_set(v___f_1896_, 6, v_postApp_1879_);
lean_closure_set(v___f_1896_, 7, v_body_1891_);
v___x_1897_ = lean_expr_instantiate_rev(v_binderType_1890_, v_fvars_1880_);
lean_dec_ref(v_fvars_1880_);
lean_dec_ref(v_binderType_1890_);
v___x_1898_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1874_, v_post_1875_, v_usedLetOnly_1876_, v_skipConstInApp_1877_, v_skipInstances_1878_, v_postApp_1879_, v___x_1897_, v_a_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v_fst_1900_; lean_object* v_snd_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v_fst_1900_ = lean_ctor_get(v_a_1899_, 0);
lean_inc(v_fst_1900_);
v_snd_1901_ = lean_ctor_get(v_a_1899_, 1);
lean_inc(v_snd_1901_);
lean_dec(v_a_1899_);
v___x_1902_ = 0;
v___x_1903_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1889_, v_binderInfo_1892_, v_fst_1900_, v___f_1896_, v___x_1902_, v_a_1882_, v_snd_1901_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
return v___x_1903_;
}
else
{
lean_dec_ref(v___f_1896_);
lean_dec(v_binderName_1889_);
return v___x_1898_;
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_expr_instantiate_rev(v_e_1881_, v_fvars_1880_);
lean_dec_ref(v_e_1881_);
lean_inc_ref(v_postApp_1879_);
lean_inc_ref(v_post_1875_);
lean_inc_ref(v_pre_1874_);
v___x_1905_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1874_, v_post_1875_, v_usedLetOnly_1876_, v_skipConstInApp_1877_, v_skipInstances_1878_, v_postApp_1879_, v___x_1904_, v_a_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v_fst_1907_; lean_object* v_snd_1908_; uint8_t v___x_1909_; uint8_t v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v_fst_1907_ = lean_ctor_get(v_a_1906_, 0);
lean_inc(v_fst_1907_);
v_snd_1908_ = lean_ctor_get(v_a_1906_, 1);
lean_inc(v_snd_1908_);
lean_dec(v_a_1906_);
v___x_1909_ = 0;
v___x_1910_ = 1;
v___x_1911_ = 1;
v___x_1912_ = l_Lean_Meta_mkForallFVars(v_fvars_1880_, v_fst_1907_, v___x_1909_, v_usedLetOnly_1876_, v___x_1910_, v___x_1911_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
lean_dec_ref(v_fvars_1880_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1874_, v_post_1875_, v_usedLetOnly_1876_, v_skipConstInApp_1877_, v_skipInstances_1878_, v_postApp_1879_, v_a_1913_, v_a_1882_, v_snd_1908_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
return v___x_1914_;
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_snd_1908_);
lean_dec_ref(v_postApp_1879_);
lean_dec_ref(v_post_1875_);
lean_dec_ref(v_pre_1874_);
v_a_1915_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1912_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1912_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1880_);
lean_dec_ref(v_postApp_1879_);
lean_dec_ref(v_post_1875_);
lean_dec_ref(v_pre_1874_);
return v___x_1905_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1923_, lean_object* v_pre_1924_, lean_object* v_post_1925_, uint8_t v_usedLetOnly_1926_, uint8_t v_skipConstInApp_1927_, uint8_t v_skipInstances_1928_, lean_object* v_postApp_1929_, lean_object* v_body_1930_, lean_object* v_x_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_array_push(v_fvars_1923_, v_x_1931_);
v___x_1940_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1924_, v_post_1925_, v_usedLetOnly_1926_, v_skipConstInApp_1927_, v_skipInstances_1928_, v_postApp_1929_, v___x_1939_, v_body_1930_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1941_, lean_object* v_post_1942_, lean_object* v_usedLetOnly_1943_, lean_object* v_skipConstInApp_1944_, lean_object* v_skipInstances_1945_, lean_object* v_postApp_1946_, lean_object* v_sz_1947_, lean_object* v_i_1948_, lean_object* v_bs_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
uint8_t v_usedLetOnly_boxed_1957_; uint8_t v_skipConstInApp_boxed_1958_; uint8_t v_skipInstances_boxed_1959_; size_t v_sz_boxed_1960_; size_t v_i_boxed_1961_; lean_object* v_res_1962_; 
v_usedLetOnly_boxed_1957_ = lean_unbox(v_usedLetOnly_1943_);
v_skipConstInApp_boxed_1958_ = lean_unbox(v_skipConstInApp_1944_);
v_skipInstances_boxed_1959_ = lean_unbox(v_skipInstances_1945_);
v_sz_boxed_1960_ = lean_unbox_usize(v_sz_1947_);
lean_dec(v_sz_1947_);
v_i_boxed_1961_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_res_1962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1941_, v_post_1942_, v_usedLetOnly_boxed_1957_, v_skipConstInApp_boxed_1958_, v_skipInstances_boxed_1959_, v_postApp_1946_, v_sz_boxed_1960_, v_i_boxed_1961_, v_bs_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1950_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object* v_pre_1963_, lean_object* v_post_1964_, lean_object* v_usedLetOnly_1965_, lean_object* v_skipConstInApp_1966_, lean_object* v_skipInstances_1967_, lean_object* v_postApp_1968_, lean_object* v_e_1969_, lean_object* v_a_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
uint8_t v_usedLetOnly_boxed_1977_; uint8_t v_skipConstInApp_boxed_1978_; uint8_t v_skipInstances_boxed_1979_; lean_object* v_res_1980_; 
v_usedLetOnly_boxed_1977_ = lean_unbox(v_usedLetOnly_1965_);
v_skipConstInApp_boxed_1978_ = lean_unbox(v_skipConstInApp_1966_);
v_skipInstances_boxed_1979_ = lean_unbox(v_skipInstances_1967_);
v_res_1980_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1963_, v_post_1964_, v_usedLetOnly_boxed_1977_, v_skipConstInApp_boxed_1978_, v_skipInstances_boxed_1979_, v_postApp_1968_, v_e_1969_, v_a_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v_a_1970_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1981_, lean_object* v_post_1982_, lean_object* v_usedLetOnly_1983_, lean_object* v_skipConstInApp_1984_, lean_object* v_skipInstances_1985_, lean_object* v_postApp_1986_, lean_object* v_fvars_1987_, lean_object* v_e_1988_, lean_object* v_a_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
uint8_t v_usedLetOnly_boxed_1996_; uint8_t v_skipConstInApp_boxed_1997_; uint8_t v_skipInstances_boxed_1998_; lean_object* v_res_1999_; 
v_usedLetOnly_boxed_1996_ = lean_unbox(v_usedLetOnly_1983_);
v_skipConstInApp_boxed_1997_ = lean_unbox(v_skipConstInApp_1984_);
v_skipInstances_boxed_1998_ = lean_unbox(v_skipInstances_1985_);
v_res_1999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1981_, v_post_1982_, v_usedLetOnly_boxed_1996_, v_skipConstInApp_boxed_1997_, v_skipInstances_boxed_1998_, v_postApp_1986_, v_fvars_1987_, v_e_1988_, v_a_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v_a_1989_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_2000_, lean_object* v_post_2001_, lean_object* v_usedLetOnly_2002_, lean_object* v_skipConstInApp_2003_, lean_object* v_skipInstances_2004_, lean_object* v_postApp_2005_, lean_object* v_fvars_2006_, lean_object* v_e_2007_, lean_object* v_a_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v_usedLetOnly_boxed_2015_; uint8_t v_skipConstInApp_boxed_2016_; uint8_t v_skipInstances_boxed_2017_; lean_object* v_res_2018_; 
v_usedLetOnly_boxed_2015_ = lean_unbox(v_usedLetOnly_2002_);
v_skipConstInApp_boxed_2016_ = lean_unbox(v_skipConstInApp_2003_);
v_skipInstances_boxed_2017_ = lean_unbox(v_skipInstances_2004_);
v_res_2018_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_2000_, v_post_2001_, v_usedLetOnly_boxed_2015_, v_skipConstInApp_boxed_2016_, v_skipInstances_boxed_2017_, v_postApp_2005_, v_fvars_2006_, v_e_2007_, v_a_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v_a_2008_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_2019_, lean_object* v_post_2020_, lean_object* v_usedLetOnly_2021_, lean_object* v_skipConstInApp_2022_, lean_object* v_skipInstances_2023_, lean_object* v_postApp_2024_, lean_object* v_e_2025_, lean_object* v_a_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
uint8_t v_usedLetOnly_boxed_2033_; uint8_t v_skipConstInApp_boxed_2034_; uint8_t v_skipInstances_boxed_2035_; lean_object* v_res_2036_; 
v_usedLetOnly_boxed_2033_ = lean_unbox(v_usedLetOnly_2021_);
v_skipConstInApp_boxed_2034_ = lean_unbox(v_skipConstInApp_2022_);
v_skipInstances_boxed_2035_ = lean_unbox(v_skipInstances_2023_);
v_res_2036_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2019_, v_post_2020_, v_usedLetOnly_boxed_2033_, v_skipConstInApp_boxed_2034_, v_skipInstances_boxed_2035_, v_postApp_2024_, v_e_2025_, v_a_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v_a_2026_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_2037_, lean_object* v_post_2038_, lean_object* v_usedLetOnly_2039_, lean_object* v_skipConstInApp_2040_, lean_object* v_skipInstances_2041_, lean_object* v_postApp_2042_, lean_object* v_fvars_2043_, lean_object* v_e_2044_, lean_object* v_a_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
uint8_t v_usedLetOnly_boxed_2052_; uint8_t v_skipConstInApp_boxed_2053_; uint8_t v_skipInstances_boxed_2054_; lean_object* v_res_2055_; 
v_usedLetOnly_boxed_2052_ = lean_unbox(v_usedLetOnly_2039_);
v_skipConstInApp_boxed_2053_ = lean_unbox(v_skipConstInApp_2040_);
v_skipInstances_boxed_2054_ = lean_unbox(v_skipInstances_2041_);
v_res_2055_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_2037_, v_post_2038_, v_usedLetOnly_boxed_2052_, v_skipConstInApp_boxed_2053_, v_skipInstances_boxed_2054_, v_postApp_2042_, v_fvars_2043_, v_e_2044_, v_a_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v_a_2045_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_2056_ = _args[0];
lean_object* v___x_2057_ = _args[1];
lean_object* v_pre_2058_ = _args[2];
lean_object* v_post_2059_ = _args[3];
lean_object* v_usedLetOnly_2060_ = _args[4];
lean_object* v_skipConstInApp_2061_ = _args[5];
lean_object* v_skipInstances_2062_ = _args[6];
lean_object* v_postApp_2063_ = _args[7];
lean_object* v_a_2064_ = _args[8];
lean_object* v_b_2065_ = _args[9];
lean_object* v___y_2066_ = _args[10];
lean_object* v___y_2067_ = _args[11];
lean_object* v___y_2068_ = _args[12];
lean_object* v___y_2069_ = _args[13];
lean_object* v___y_2070_ = _args[14];
lean_object* v___y_2071_ = _args[15];
lean_object* v___y_2072_ = _args[16];
_start:
{
uint8_t v_usedLetOnly_boxed_2073_; uint8_t v_skipConstInApp_boxed_2074_; uint8_t v_skipInstances_boxed_2075_; lean_object* v_res_2076_; 
v_usedLetOnly_boxed_2073_ = lean_unbox(v_usedLetOnly_2060_);
v_skipConstInApp_boxed_2074_ = lean_unbox(v_skipConstInApp_2061_);
v_skipInstances_boxed_2075_ = lean_unbox(v_skipInstances_2062_);
v_res_2076_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_upperBound_2056_, v___x_2057_, v_pre_2058_, v_post_2059_, v_usedLetOnly_boxed_2073_, v_skipConstInApp_boxed_2074_, v_skipInstances_boxed_2075_, v_postApp_2063_, v_a_2064_, v_b_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2066_);
lean_dec_ref(v___x_2057_);
lean_dec(v_upperBound_2056_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object** _args){
lean_object* v_skipInstances_2077_ = _args[0];
lean_object* v_pre_2078_ = _args[1];
lean_object* v_post_2079_ = _args[2];
lean_object* v_usedLetOnly_2080_ = _args[3];
lean_object* v_skipConstInApp_2081_ = _args[4];
lean_object* v_postApp_2082_ = _args[5];
lean_object* v___y_2083_ = _args[6];
lean_object* v_x_2084_ = _args[7];
lean_object* v_x_2085_ = _args[8];
lean_object* v_x_2086_ = _args[9];
lean_object* v___y_2087_ = _args[10];
lean_object* v___y_2088_ = _args[11];
lean_object* v___y_2089_ = _args[12];
lean_object* v___y_2090_ = _args[13];
lean_object* v___y_2091_ = _args[14];
lean_object* v___y_2092_ = _args[15];
lean_object* v___y_2093_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2094_; uint8_t v_usedLetOnly_boxed_2095_; uint8_t v_skipConstInApp_boxed_2096_; lean_object* v_res_2097_; 
v_skipInstances_boxed_2094_ = lean_unbox(v_skipInstances_2077_);
v_usedLetOnly_boxed_2095_ = lean_unbox(v_usedLetOnly_2080_);
v_skipConstInApp_boxed_2096_ = lean_unbox(v_skipConstInApp_2081_);
v_res_2097_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2094_, v_pre_2078_, v_post_2079_, v_usedLetOnly_boxed_2095_, v_skipConstInApp_boxed_2096_, v_postApp_2082_, v___y_2083_, v_x_2084_, v_x_2085_, v_x_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2087_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2098_, lean_object* v_x_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = lean_apply_1(v_x_2099_, lean_box(0));
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___y_2100_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2109_, lean_object* v_x_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2109_, v_x_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__1(lean_object* v_x_2118_, lean_object* v_e_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_e_2119_);
lean_ctor_set(v___x_2126_, 1, v___y_2120_);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__1___boxed(lean_object* v_x_2128_, lean_object* v_e_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__1(v_x_2128_, v_e_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec_ref(v_x_2128_);
return v_res_2136_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lean_box(0);
v___x_2139_ = lean_unsigned_to_nat(16u);
v___x_2140_ = lean_mk_array(v___x_2139_, v___x_2138_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v___x_2141_);
return v___x_2143_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2145_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2145_, 0, lean_box(0));
lean_closure_set(v___x_2145_, 1, lean_box(0));
lean_closure_set(v___x_2145_, 2, v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2146_, lean_object* v_pre_2147_, lean_object* v_post_2148_, uint8_t v_usedLetOnly_2149_, uint8_t v_skipConstInApp_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___f_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v_a_2161_; lean_object* v_fst_2162_; lean_object* v_snd_2163_; lean_object* v___x_2164_; 
v___f_2157_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0));
v___x_2158_ = 0;
v___x_2159_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3);
v___x_2160_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2159_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref(v___x_2160_);
v_fst_2162_ = lean_ctor_get(v_a_2161_, 0);
lean_inc(v_fst_2162_);
v_snd_2163_ = lean_ctor_get(v_a_2161_, 1);
lean_inc(v_snd_2163_);
lean_dec(v_a_2161_);
v___x_2164_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2147_, v_post_2148_, v_usedLetOnly_2149_, v_skipConstInApp_2150_, v___x_2158_, v___f_2157_, v_input_2146_, v_fst_2162_, v_snd_2163_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v_fst_2166_; lean_object* v_snd_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2186_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v_fst_2166_ = lean_ctor_get(v_a_2165_, 0);
lean_inc(v_fst_2166_);
v_snd_2167_ = lean_ctor_get(v_a_2165_, 1);
lean_inc(v_snd_2167_);
lean_dec(v_a_2165_);
v___x_2168_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2168_, 0, lean_box(0));
lean_closure_set(v___x_2168_, 1, lean_box(0));
lean_closure_set(v___x_2168_, 2, v_fst_2162_);
v___x_2169_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2168_, v_snd_2167_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2186_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2186_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_snd_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2184_; 
v_snd_2174_ = lean_ctor_get(v_a_2170_, 1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_a_2170_);
if (v_isSharedCheck_2184_ == 0)
{
lean_object* v_unused_2185_; 
v_unused_2185_ = lean_ctor_get(v_a_2170_, 0);
lean_dec(v_unused_2185_);
v___x_2176_ = v_a_2170_;
v_isShared_2177_ = v_isSharedCheck_2184_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_snd_2174_);
lean_dec(v_a_2170_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2184_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v_fst_2166_);
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_fst_2166_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_snd_2174_);
v___x_2179_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2181_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2179_);
v___x_2181_ = v___x_2172_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
else
{
lean_dec(v_fst_2162_);
return v___x_2164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2187_, lean_object* v_pre_2188_, lean_object* v_post_2189_, lean_object* v_usedLetOnly_2190_, lean_object* v_skipConstInApp_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
uint8_t v_usedLetOnly_boxed_2198_; uint8_t v_skipConstInApp_boxed_2199_; lean_object* v_res_2200_; 
v_usedLetOnly_boxed_2198_ = lean_unbox(v_usedLetOnly_2190_);
v_skipConstInApp_boxed_2199_ = lean_unbox(v_skipConstInApp_2191_);
v_res_2200_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2187_, v_pre_2188_, v_post_2189_, v_usedLetOnly_boxed_2198_, v_skipConstInApp_boxed_2199_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v___y_2210_; lean_object* v___x_2227_; uint8_t v_transparency_2228_; lean_object* v___f_2229_; lean_object* v___f_2230_; uint8_t v___x_2231_; uint8_t v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2227_ = l_Lean_Meta_Context_config(v_a_2204_);
v_transparency_2228_ = lean_ctor_get_uint8(v___x_2227_, 9);
lean_dec_ref(v___x_2227_);
v___f_2229_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2230_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2231_ = 0;
v___x_2232_ = 3;
v___x_2233_ = lean_box(0);
v___x_2234_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2228_, v___x_2232_);
if (v___x_2234_ == 0)
{
lean_object* v_keyedConfig_2235_; uint8_t v_trackZetaDelta_2236_; lean_object* v_zetaDeltaSet_2237_; lean_object* v_lctx_2238_; lean_object* v_localInstances_2239_; lean_object* v_defEqCtx_x3f_2240_; lean_object* v_synthPendingDepth_2241_; lean_object* v_customCanUnfoldPredicate_x3f_2242_; uint8_t v_univApprox_2243_; uint8_t v_inTypeClassResolution_2244_; uint8_t v_cacheInferType_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_keyedConfig_2235_ = lean_ctor_get(v_a_2204_, 0);
v_trackZetaDelta_2236_ = lean_ctor_get_uint8(v_a_2204_, sizeof(void*)*7);
v_zetaDeltaSet_2237_ = lean_ctor_get(v_a_2204_, 1);
v_lctx_2238_ = lean_ctor_get(v_a_2204_, 2);
v_localInstances_2239_ = lean_ctor_get(v_a_2204_, 3);
v_defEqCtx_x3f_2240_ = lean_ctor_get(v_a_2204_, 4);
v_synthPendingDepth_2241_ = lean_ctor_get(v_a_2204_, 5);
v_customCanUnfoldPredicate_x3f_2242_ = lean_ctor_get(v_a_2204_, 6);
v_univApprox_2243_ = lean_ctor_get_uint8(v_a_2204_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2244_ = lean_ctor_get_uint8(v_a_2204_, sizeof(void*)*7 + 2);
v_cacheInferType_2245_ = lean_ctor_get_uint8(v_a_2204_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2235_);
v___x_2246_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2232_, v_keyedConfig_2235_);
lean_inc(v_customCanUnfoldPredicate_x3f_2242_);
lean_inc(v_synthPendingDepth_2241_);
lean_inc(v_defEqCtx_x3f_2240_);
lean_inc_ref(v_localInstances_2239_);
lean_inc_ref(v_lctx_2238_);
lean_inc(v_zetaDeltaSet_2237_);
v___x_2247_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v_zetaDeltaSet_2237_);
lean_ctor_set(v___x_2247_, 2, v_lctx_2238_);
lean_ctor_set(v___x_2247_, 3, v_localInstances_2239_);
lean_ctor_set(v___x_2247_, 4, v_defEqCtx_x3f_2240_);
lean_ctor_set(v___x_2247_, 5, v_synthPendingDepth_2241_);
lean_ctor_set(v___x_2247_, 6, v_customCanUnfoldPredicate_x3f_2242_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*7, v_trackZetaDelta_2236_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*7 + 1, v_univApprox_2243_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2244_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*7 + 3, v_cacheInferType_2245_);
v___x_2248_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2203_, v___f_2230_, v___f_2229_, v___x_2231_, v___x_2231_, v___x_2233_, v___x_2247_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec_ref_known(v___x_2247_, 7);
v___y_2210_ = v___x_2248_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2203_, v___f_2230_, v___f_2229_, v___x_2231_, v___x_2231_, v___x_2233_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
v___y_2210_ = v___x_2249_;
goto v___jp_2209_;
}
v___jp_2209_:
{
if (lean_obj_tag(v___y_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
v_a_2211_ = lean_ctor_get(v___y_2210_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___y_2210_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___y_2210_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___y_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
v_a_2219_ = lean_ctor_get(v___y_2210_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___y_2210_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___y_2210_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___y_2210_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Meta_expandCoe(v_e_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2257_, lean_object* v_m_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2258_, v_a_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2261_, lean_object* v_m_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2261_, v_m_2262_, v_a_2263_);
lean_dec(v_a_2263_);
lean_dec_ref(v_m_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_){
_start:
{
uint8_t v___x_2268_; 
v___x_2268_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2266_, v_x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2269_, lean_object* v_x_2270_, lean_object* v_x_2271_){
_start:
{
uint8_t v_res_2272_; lean_object* v_r_2273_; 
v_res_2272_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2269_, v_x_2270_, v_x_2271_);
lean_dec_ref(v_x_2271_);
lean_dec_ref(v_x_2270_);
v_r_2273_ = lean_box(v_res_2272_);
return v_r_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2274_, lean_object* v_a_2275_, lean_object* v_x_2276_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2275_, v_x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2278_, lean_object* v_a_2279_, lean_object* v_x_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2278_, v_a_2279_, v_x_2280_);
lean_dec(v_x_2280_);
lean_dec(v_a_2279_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_2282_, lean_object* v_m_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___redArg(v_m_2283_, v_a_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2286_, lean_object* v_m_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_00_u03b2_2286_, v_m_2287_, v_a_2288_);
lean_dec_ref(v_a_2288_);
lean_dec_ref(v_m_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_upperBound_2290_, lean_object* v___x_2291_, lean_object* v_pre_2292_, lean_object* v_post_2293_, uint8_t v_usedLetOnly_2294_, uint8_t v_skipConstInApp_2295_, uint8_t v_skipInstances_2296_, lean_object* v_postApp_2297_, lean_object* v___x_2298_, lean_object* v_inst_2299_, lean_object* v_R_2300_, lean_object* v_a_2301_, lean_object* v_b_2302_, lean_object* v_c_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_upperBound_2290_, v___x_2291_, v_pre_2292_, v_post_2293_, v_usedLetOnly_2294_, v_skipConstInApp_2295_, v_skipInstances_2296_, v_postApp_2297_, v_a_2301_, v_b_2302_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object** _args){
lean_object* v_upperBound_2312_ = _args[0];
lean_object* v___x_2313_ = _args[1];
lean_object* v_pre_2314_ = _args[2];
lean_object* v_post_2315_ = _args[3];
lean_object* v_usedLetOnly_2316_ = _args[4];
lean_object* v_skipConstInApp_2317_ = _args[5];
lean_object* v_skipInstances_2318_ = _args[6];
lean_object* v_postApp_2319_ = _args[7];
lean_object* v___x_2320_ = _args[8];
lean_object* v_inst_2321_ = _args[9];
lean_object* v_R_2322_ = _args[10];
lean_object* v_a_2323_ = _args[11];
lean_object* v_b_2324_ = _args[12];
lean_object* v_c_2325_ = _args[13];
lean_object* v___y_2326_ = _args[14];
lean_object* v___y_2327_ = _args[15];
lean_object* v___y_2328_ = _args[16];
lean_object* v___y_2329_ = _args[17];
lean_object* v___y_2330_ = _args[18];
lean_object* v___y_2331_ = _args[19];
lean_object* v___y_2332_ = _args[20];
_start:
{
uint8_t v_usedLetOnly_boxed_2333_; uint8_t v_skipConstInApp_boxed_2334_; uint8_t v_skipInstances_boxed_2335_; lean_object* v_res_2336_; 
v_usedLetOnly_boxed_2333_ = lean_unbox(v_usedLetOnly_2316_);
v_skipConstInApp_boxed_2334_ = lean_unbox(v_skipConstInApp_2317_);
v_skipInstances_boxed_2335_ = lean_unbox(v_skipInstances_2318_);
v_res_2336_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_upperBound_2312_, v___x_2313_, v_pre_2314_, v_post_2315_, v_usedLetOnly_boxed_2333_, v_skipConstInApp_boxed_2334_, v_skipInstances_boxed_2335_, v_postApp_2319_, v___x_2320_, v_inst_2321_, v_R_2322_, v_a_2323_, v_b_2324_, v_c_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2326_);
lean_dec(v___x_2320_);
lean_dec_ref(v___x_2313_);
lean_dec(v_upperBound_2312_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2337_, lean_object* v_name_2338_, uint8_t v_bi_2339_, lean_object* v_type_2340_, lean_object* v_k_2341_, uint8_t v_kind_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2338_, v_bi_2339_, v_type_2340_, v_k_2341_, v_kind_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2351_, lean_object* v_name_2352_, lean_object* v_bi_2353_, lean_object* v_type_2354_, lean_object* v_k_2355_, lean_object* v_kind_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
uint8_t v_bi_boxed_2364_; uint8_t v_kind_boxed_2365_; lean_object* v_res_2366_; 
v_bi_boxed_2364_ = lean_unbox(v_bi_2353_);
v_kind_boxed_2365_ = lean_unbox(v_kind_2356_);
v_res_2366_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2351_, v_name_2352_, v_bi_boxed_2364_, v_type_2354_, v_k_2355_, v_kind_boxed_2365_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2357_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2367_, lean_object* v_name_2368_, lean_object* v_type_2369_, lean_object* v_val_2370_, lean_object* v_k_2371_, uint8_t v_nondep_2372_, uint8_t v_kind_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2368_, v_type_2369_, v_val_2370_, v_k_2371_, v_nondep_2372_, v_kind_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2382_, lean_object* v_name_2383_, lean_object* v_type_2384_, lean_object* v_val_2385_, lean_object* v_k_2386_, lean_object* v_nondep_2387_, lean_object* v_kind_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
uint8_t v_nondep_boxed_2396_; uint8_t v_kind_boxed_2397_; lean_object* v_res_2398_; 
v_nondep_boxed_2396_ = lean_unbox(v_nondep_2387_);
v_kind_boxed_2397_ = lean_unbox(v_kind_2388_);
v_res_2398_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2382_, v_name_2383_, v_type_2384_, v_val_2385_, v_k_2386_, v_nondep_boxed_2396_, v_kind_boxed_2397_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2389_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2399_, lean_object* v_ref_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2400_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2407_, lean_object* v_ref_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2407_, v_ref_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2415_, lean_object* v_x_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2425_, lean_object* v_x_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2425_, v_x_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2427_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2435_, lean_object* v_m_2436_, lean_object* v_a_2437_, lean_object* v_b_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2436_, v_a_2437_, v_b_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2440_, lean_object* v_x_2441_, size_t v_x_2442_, lean_object* v_x_2443_){
_start:
{
uint8_t v___x_2444_; 
v___x_2444_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2441_, v_x_2442_, v_x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_, lean_object* v_x_2448_){
_start:
{
size_t v_x_41390__boxed_2449_; uint8_t v_res_2450_; lean_object* v_r_2451_; 
v_x_41390__boxed_2449_ = lean_unbox_usize(v_x_2447_);
lean_dec(v_x_2447_);
v_res_2450_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2445_, v_x_2446_, v_x_41390__boxed_2449_, v_x_2448_);
lean_dec_ref(v_x_2448_);
lean_dec_ref(v_x_2446_);
v_r_2451_ = lean_box(v_res_2450_);
return v_r_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_2452_, lean_object* v_a_2453_, lean_object* v_x_2454_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11___redArg(v_a_2453_, v_x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2456_, lean_object* v_a_2457_, lean_object* v_x_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_spec__11(v_00_u03b2_2456_, v_a_2457_, v_x_2458_);
lean_dec(v_x_2458_);
lean_dec_ref(v_a_2457_);
return v_res_2459_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2460_, lean_object* v_a_2461_, lean_object* v_x_2462_){
_start:
{
uint8_t v___x_2463_; 
v___x_2463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2461_, v_x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2464_, lean_object* v_a_2465_, lean_object* v_x_2466_){
_start:
{
uint8_t v_res_2467_; lean_object* v_r_2468_; 
v_res_2467_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2464_, v_a_2465_, v_x_2466_);
lean_dec(v_x_2466_);
lean_dec_ref(v_a_2465_);
v_r_2468_ = lean_box(v_res_2467_);
return v_r_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2469_, lean_object* v_data_2470_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2472_, lean_object* v_a_2473_, lean_object* v_b_2474_, lean_object* v_x_2475_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2473_, v_b_2474_, v_x_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2477_, lean_object* v_keys_2478_, lean_object* v_vals_2479_, lean_object* v_heq_2480_, lean_object* v_i_2481_, lean_object* v_k_2482_){
_start:
{
uint8_t v___x_2483_; 
v___x_2483_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2478_, v_i_2481_, v_k_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2484_, lean_object* v_keys_2485_, lean_object* v_vals_2486_, lean_object* v_heq_2487_, lean_object* v_i_2488_, lean_object* v_k_2489_){
_start:
{
uint8_t v_res_2490_; lean_object* v_r_2491_; 
v_res_2490_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2484_, v_keys_2485_, v_vals_2486_, v_heq_2487_, v_i_2488_, v_k_2489_);
lean_dec_ref(v_k_2489_);
lean_dec_ref(v_vals_2486_);
lean_dec_ref(v_keys_2485_);
v_r_2491_ = lean_box(v_res_2490_);
return v_r_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2492_, lean_object* v_i_2493_, lean_object* v_source_2494_, lean_object* v_target_2495_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2493_, v_source_2494_, v_target_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2497_, lean_object* v_x_2498_, lean_object* v_x_2499_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2498_, v_x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2501_, lean_object* v_decl_2502_, lean_object* v_ref_2503_){
_start:
{
lean_object* v_defValue_2505_; lean_object* v_descr_2506_; lean_object* v_deprecation_x3f_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_defValue_2505_ = lean_ctor_get(v_decl_2502_, 0);
v_descr_2506_ = lean_ctor_get(v_decl_2502_, 1);
v_deprecation_x3f_2507_ = lean_ctor_get(v_decl_2502_, 2);
v___x_2508_ = lean_alloc_ctor(1, 0, 1);
v___x_2509_ = lean_unbox(v_defValue_2505_);
lean_ctor_set_uint8(v___x_2508_, 0, v___x_2509_);
lean_inc(v_deprecation_x3f_2507_);
lean_inc_ref(v_descr_2506_);
lean_inc_n(v_name_2501_, 2);
v___x_2510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2510_, 0, v_name_2501_);
lean_ctor_set(v___x_2510_, 1, v_ref_2503_);
lean_ctor_set(v___x_2510_, 2, v___x_2508_);
lean_ctor_set(v___x_2510_, 3, v_descr_2506_);
lean_ctor_set(v___x_2510_, 4, v_deprecation_x3f_2507_);
v___x_2511_ = lean_register_option(v_name_2501_, v___x_2510_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2519_; 
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v___x_2511_, 0);
lean_dec(v_unused_2520_);
v___x_2513_ = v___x_2511_;
v_isShared_2514_ = v_isSharedCheck_2519_;
goto v_resetjp_2512_;
}
else
{
lean_dec(v___x_2511_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2519_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
lean_inc(v_defValue_2505_);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v_name_2501_);
lean_ctor_set(v___x_2515_, 1, v_defValue_2505_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2515_);
v___x_2517_ = v___x_2513_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec(v_name_2501_);
v_a_2521_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2511_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2511_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2529_, lean_object* v_decl_2530_, lean_object* v_ref_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2529_, v_decl_2530_, v_ref_2531_);
lean_dec_ref(v_decl_2530_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2548_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2549_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2550_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2551_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2548_, v___x_2549_, v___x_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_ref_2560_; lean_object* v___x_2561_; lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2570_; 
v_ref_2560_ = lean_ctor_get(v___y_2557_, 2);
v___x_2561_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
lean_inc(v_ref_2560_);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_ref_2560_);
lean_ctor_set(v___x_2566_, 1, v_a_2562_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set_tag(v___x_2564_, 1);
lean_ctor_set(v___x_2564_, 0, v___x_2566_);
v___x_2568_ = v___x_2564_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
return v_res_2577_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2586_ = l_Lean_stringToMessageData(v___x_2585_);
return v___x_2586_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2589_ = l_Lean_stringToMessageData(v___x_2588_);
return v___x_2589_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2592_ = l_Lean_stringToMessageData(v___x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2593_, lean_object* v_expectedType_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_){
_start:
{
lean_object* v___x_2600_; 
lean_inc(v_a_2598_);
lean_inc_ref(v_a_2597_);
lean_inc(v_a_2596_);
lean_inc_ref(v_a_2595_);
lean_inc_ref(v_expr_2593_);
v___x_2600_ = lean_infer_type(v_expr_2593_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc_n(v_a_2601_, 2);
lean_dec_ref_known(v___x_2600_, 1);
v___x_2602_ = l_Lean_Meta_getLevel(v_a_2601_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2604_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2602_, 1);
lean_inc_ref(v_expectedType_2594_);
v___x_2604_ = l_Lean_Meta_getLevel(v_expectedType_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2608_, 0, v_a_2605_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_a_2603_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
lean_inc_ref(v___x_2609_);
v___x_2610_ = l_Lean_mkConst(v___x_2606_, v___x_2609_);
v___x_2611_ = lean_unsigned_to_nat(3u);
v___x_2612_ = lean_mk_empty_array_with_capacity(v___x_2611_);
lean_inc(v_a_2601_);
v___x_2613_ = lean_array_push(v___x_2612_, v_a_2601_);
lean_inc_ref(v_expr_2593_);
v___x_2614_ = lean_array_push(v___x_2613_, v_expr_2593_);
lean_inc_ref(v_expectedType_2594_);
v___x_2615_ = lean_array_push(v___x_2614_, v_expectedType_2594_);
v___x_2616_ = l_Lean_mkAppN(v___x_2610_, v___x_2615_);
lean_dec_ref(v___x_2615_);
v___x_2617_ = lean_box(0);
v___x_2618_ = l_Lean_Meta_trySynthInstance(v___x_2616_, v___x_2617_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2716_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2716_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2716_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
switch(lean_obj_tag(v_a_2619_))
{
case 0:
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_dec_ref_known(v___x_2609_, 2);
lean_dec(v_a_2601_);
lean_dec_ref(v_expectedType_2594_);
lean_dec_ref(v_expr_2593_);
v___x_2623_ = lean_box(0);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2625_ = v___x_2621_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
case 1:
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2711_; 
lean_del_object(v___x_2621_);
v_a_2627_ = lean_ctor_get(v_a_2619_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_a_2619_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2629_ = v_a_2619_;
v_isShared_2630_ = v_isSharedCheck_2711_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v_a_2619_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2711_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2631_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2632_ = l_Lean_mkConst(v___x_2631_, v___x_2609_);
v___x_2633_ = lean_unsigned_to_nat(4u);
v___x_2634_ = lean_mk_empty_array_with_capacity(v___x_2633_);
v___x_2635_ = lean_array_push(v___x_2634_, v_a_2601_);
lean_inc_ref(v_expr_2593_);
v___x_2636_ = lean_array_push(v___x_2635_, v_expr_2593_);
lean_inc_ref(v_expectedType_2594_);
v___x_2637_ = lean_array_push(v___x_2636_, v_expectedType_2594_);
v___x_2638_ = lean_array_push(v___x_2637_, v_a_2627_);
v___x_2639_ = l_Lean_mkAppN(v___x_2632_, v___x_2638_);
lean_dec_ref(v___x_2638_);
v___x_2640_ = l_Lean_Meta_expandCoe(v___x_2639_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2702_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2702_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2702_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v_fst_2652_; lean_object* v___x_2653_; 
v_fst_2652_ = lean_ctor_get(v_a_2641_, 0);
lean_inc(v_a_2598_);
lean_inc_ref(v_a_2597_);
lean_inc(v_a_2596_);
lean_inc_ref(v_a_2595_);
lean_inc(v_fst_2652_);
v___x_2653_ = lean_infer_type(v_fst_2652_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2655_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
lean_inc_ref(v_expectedType_2594_);
v___x_2655_ = l_Lean_Meta_isExprDefEq(v_a_2654_, v_expectedType_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; uint8_t v___x_2657_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v___x_2657_ = lean_unbox(v_a_2656_);
lean_dec(v_a_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2683_; 
lean_inc(v_fst_2652_);
lean_del_object(v___x_2643_);
lean_del_object(v___x_2629_);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_a_2641_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; lean_object* v_unused_2685_; 
v_unused_2684_ = lean_ctor_get(v_a_2641_, 1);
lean_dec(v_unused_2684_);
v_unused_2685_ = lean_ctor_get(v_a_2641_, 0);
lean_dec(v_unused_2685_);
v___x_2659_ = v_a_2641_;
v_isShared_2660_ = v_isSharedCheck_2683_;
goto v_resetjp_2658_;
}
else
{
lean_dec(v_a_2641_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2683_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2661_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2662_ = l_Lean_indentExpr(v_expr_2593_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set_tag(v___x_2659_, 7);
lean_ctor_set(v___x_2659_, 1, v___x_2662_);
lean_ctor_set(v___x_2659_, 0, v___x_2661_);
v___x_2664_ = v___x_2659_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
v___x_2665_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Lean_indentExpr(v_expectedType_2594_);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = l_Lean_indentExpr(v_fst_2652_);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2672_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2673_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2594_);
lean_dec_ref(v_expr_2593_);
goto v___jp_2645_;
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_del_object(v___x_2643_);
lean_dec(v_a_2641_);
lean_del_object(v___x_2629_);
lean_dec_ref(v_expectedType_2594_);
lean_dec_ref(v_expr_2593_);
v_a_2686_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2655_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2655_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_del_object(v___x_2643_);
lean_dec(v_a_2641_);
lean_del_object(v___x_2629_);
lean_dec_ref(v_expectedType_2594_);
lean_dec_ref(v_expr_2593_);
v_a_2694_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2653_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2653_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
v___jp_2645_:
{
lean_object* v___x_2647_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v_a_2641_);
v___x_2647_ = v___x_2629_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2641_);
v___x_2647_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2649_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2647_);
v___x_2649_ = v___x_2643_;
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
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_del_object(v___x_2629_);
lean_dec_ref(v_expectedType_2594_);
lean_dec_ref(v_expr_2593_);
v_a_2703_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2640_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2640_);
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
default: 
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
lean_dec_ref_known(v___x_2609_, 2);
lean_dec(v_a_2601_);
lean_dec_ref(v_expectedType_2594_);
lean_dec_ref(v_expr_2593_);
v___x_2712_ = lean_box(2);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2712_);
v___x_2714_ = v___x_2621_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec_ref_known(v___x_2609_, 2);
lean_dec(v_a_2601_);
lean_dec_ref(v_expectedType_2594_);
lean_dec_ref(v_expr_2593_);
v_a_2717_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2618_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2618_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_a_2603_);
lean_dec(v_a_2601_);
lean_dec_ref(v_expectedType_2594_);
lean_dec_ref(v_expr_2593_);
v_a_2725_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2604_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2604_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v_a_2601_);
lean_dec_ref(v_expectedType_2594_);
lean_dec_ref(v_expr_2593_);
v_a_2733_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2602_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2602_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
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
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref(v_expectedType_2594_);
lean_dec_ref(v_expr_2593_);
v_a_2741_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2600_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2600_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2749_, lean_object* v_expectedType_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2749_, v_expectedType_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2757_, lean_object* v_msg_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2765_, lean_object* v_msg_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2765_, v_msg_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2773_, lean_object* v_expectedType_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2773_, v_expectedType_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2805_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2805_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2805_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
switch(lean_obj_tag(v_a_2781_))
{
case 0:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = lean_box(0);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2785_);
v___x_2787_ = v___x_2783_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
case 1:
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2800_; 
v_a_2789_ = lean_ctor_get(v_a_2781_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_a_2781_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2791_ = v_a_2781_;
v_isShared_2792_ = v_isSharedCheck_2800_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v_a_2781_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2800_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v_fst_2793_; lean_object* v___x_2795_; 
v_fst_2793_ = lean_ctor_get(v_a_2789_, 0);
lean_inc(v_fst_2793_);
lean_dec(v_a_2789_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v_fst_2793_);
v___x_2795_ = v___x_2791_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_fst_2793_);
v___x_2795_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2797_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2795_);
v___x_2797_ = v___x_2783_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
default: 
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2801_ = lean_box(2);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2801_);
v___x_2803_ = v___x_2783_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
v_a_2806_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2780_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2780_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2814_, lean_object* v_expectedType_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2814_, v_expectedType_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
return v_res_2821_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2830_ = l_Lean_stringToMessageData(v___x_2829_);
return v___x_2830_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2833_ = l_Lean_stringToMessageData(v___x_2832_);
return v___x_2833_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2836_ = l_Lean_stringToMessageData(v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v___x_2843_; 
lean_inc(v_a_2841_);
lean_inc_ref(v_a_2840_);
lean_inc(v_a_2839_);
lean_inc_ref(v_a_2838_);
lean_inc_ref(v_expr_2837_);
v___x_2843_ = lean_infer_type(v_expr_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc_n(v_a_2844_, 2);
lean_dec_ref_known(v___x_2843_, 1);
v___x_2845_ = l_Lean_Meta_getLevel(v_a_2844_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2847_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2845_, 1);
v___x_2847_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc_n(v_a_2848_, 2);
lean_dec_ref_known(v___x_2847_, 1);
v___x_2849_ = l_Lean_mkSort(v_a_2848_);
lean_inc(v_a_2844_);
v___x_2850_ = l_Lean_mkArrow(v_a_2844_, v___x_2849_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_a_2851_);
v___x_2853_ = 0;
v___x_2854_ = lean_box(0);
v___x_2855_ = l_Lean_Meta_mkFreshExprMVar(v___x_2852_, v___x_2853_, v___x_2854_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc_n(v_a_2856_, 2);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2858_ = lean_box(0);
v___x_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2859_, 0, v_a_2848_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
v___x_2860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2860_, 0, v_a_2846_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
lean_inc_ref(v___x_2860_);
v___x_2861_ = l_Lean_Expr_const___override(v___x_2857_, v___x_2860_);
lean_inc(v_a_2844_);
v___x_2862_ = l_Lean_mkAppB(v___x_2861_, v_a_2844_, v_a_2856_);
v___x_2863_ = lean_box(0);
v___x_2864_ = l_Lean_Meta_trySynthInstance(v___x_2862_, v___x_2863_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2951_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2951_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2951_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
if (lean_obj_tag(v_a_2865_) == 1)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2947_; 
lean_del_object(v___x_2867_);
v_a_2869_ = lean_ctor_get(v_a_2865_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_a_2865_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2871_ = v_a_2865_;
v_isShared_2872_ = v_isSharedCheck_2947_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v_a_2865_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2947_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2873_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2874_ = l_Lean_Expr_const___override(v___x_2873_, v___x_2860_);
lean_inc_ref(v_expr_2837_);
lean_inc(v_a_2869_);
v___x_2875_ = l_Lean_mkApp4(v___x_2874_, v_a_2844_, v_a_2856_, v_a_2869_, v_expr_2837_);
v___x_2876_ = l_Lean_Meta_expandCoe(v___x_2875_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2938_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2938_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2938_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v_fst_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2936_; 
v_fst_2881_ = lean_ctor_get(v_a_2877_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_a_2877_);
if (v_isSharedCheck_2936_ == 0)
{
lean_object* v_unused_2937_; 
v_unused_2937_ = lean_ctor_get(v_a_2877_, 1);
lean_dec(v_unused_2937_);
v___x_2883_ = v_a_2877_;
v_isShared_2884_ = v_isSharedCheck_2936_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_fst_2881_);
lean_dec(v_a_2877_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2936_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2892_; 
lean_inc(v_a_2841_);
lean_inc_ref(v_a_2840_);
lean_inc(v_a_2839_);
lean_inc_ref(v_a_2838_);
lean_inc(v_fst_2881_);
v___x_2892_ = lean_infer_type(v_fst_2881_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
lean_inc(v_a_2841_);
lean_inc_ref(v_a_2840_);
lean_inc(v_a_2839_);
lean_inc_ref(v_a_2838_);
v___x_2894_ = lean_whnf(v_a_2893_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; uint8_t v___x_2896_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = l_Lean_Expr_isForall(v_a_2895_);
lean_dec(v_a_2895_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
lean_del_object(v___x_2879_);
lean_del_object(v___x_2871_);
v___x_2897_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2898_ = l_Lean_indentExpr(v_expr_2837_);
if (v_isShared_2884_ == 0)
{
lean_ctor_set_tag(v___x_2883_, 7);
lean_ctor_set(v___x_2883_, 1, v___x_2898_);
lean_ctor_set(v___x_2883_, 0, v___x_2897_);
v___x_2900_ = v___x_2883_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
v___x_2901_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = l_Lean_indentExpr(v_fst_2881_);
v___x_2904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2906_ = l_Lean_indentExpr(v_a_2869_);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = l_Lean_MessageData_hint_x27(v___x_2907_);
v___x_2909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2904_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2909_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_del_object(v___x_2883_);
lean_dec(v_a_2869_);
lean_dec_ref(v_expr_2837_);
goto v___jp_2885_;
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_del_object(v___x_2883_);
lean_dec(v_fst_2881_);
lean_del_object(v___x_2879_);
lean_del_object(v___x_2871_);
lean_dec(v_a_2869_);
lean_dec_ref(v_expr_2837_);
v_a_2920_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2894_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2894_);
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
lean_del_object(v___x_2883_);
lean_dec(v_fst_2881_);
lean_del_object(v___x_2879_);
lean_del_object(v___x_2871_);
lean_dec(v_a_2869_);
lean_dec_ref(v_expr_2837_);
v_a_2928_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2892_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2892_);
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
v___jp_2885_:
{
lean_object* v___x_2887_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v_fst_2881_);
v___x_2887_ = v___x_2871_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_fst_2881_);
v___x_2887_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2889_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___x_2887_);
v___x_2889_ = v___x_2879_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_del_object(v___x_2871_);
lean_dec(v_a_2869_);
lean_dec_ref(v_expr_2837_);
v_a_2939_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2876_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2876_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
else
{
lean_object* v___x_2949_; 
lean_dec(v_a_2865_);
lean_dec_ref_known(v___x_2860_, 2);
lean_dec(v_a_2856_);
lean_dec(v_a_2844_);
lean_dec_ref(v_expr_2837_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2863_);
v___x_2949_ = v___x_2867_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2863_);
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
lean_dec_ref_known(v___x_2860_, 2);
lean_dec(v_a_2856_);
lean_dec(v_a_2844_);
lean_dec_ref(v_expr_2837_);
v_a_2952_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2864_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2864_);
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
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec(v_a_2848_);
lean_dec(v_a_2846_);
lean_dec(v_a_2844_);
lean_dec_ref(v_expr_2837_);
v_a_2960_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2855_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2855_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec(v_a_2848_);
lean_dec(v_a_2846_);
lean_dec(v_a_2844_);
lean_dec_ref(v_expr_2837_);
v_a_2968_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2850_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2850_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
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
lean_dec(v_a_2846_);
lean_dec(v_a_2844_);
lean_dec_ref(v_expr_2837_);
v_a_2976_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2847_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2847_);
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
lean_dec(v_a_2844_);
lean_dec_ref(v_expr_2837_);
v_a_2984_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2845_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2845_);
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
lean_dec_ref(v_expr_2837_);
v_a_2992_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2843_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2843_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
return v_res_3006_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_3015_ = l_Lean_stringToMessageData(v___x_3014_);
return v___x_3015_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_3018_ = l_Lean_stringToMessageData(v___x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v___x_3025_; 
lean_inc(v_a_3023_);
lean_inc_ref(v_a_3022_);
lean_inc(v_a_3021_);
lean_inc_ref(v_a_3020_);
lean_inc_ref(v_expr_3019_);
v___x_3025_ = lean_infer_type(v_expr_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc_n(v_a_3026_, 2);
lean_dec_ref_known(v___x_3025_, 1);
v___x_3027_ = l_Lean_Meta_getLevel(v_a_3026_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3029_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v___x_3029_ = l_Lean_Meta_mkFreshLevelMVar(v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc_n(v_a_3030_, 2);
lean_dec_ref_known(v___x_3029_, 1);
v___x_3031_ = l_Lean_mkSort(v_a_3030_);
v___x_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
v___x_3033_ = 0;
v___x_3034_ = lean_box(0);
v___x_3035_ = l_Lean_Meta_mkFreshExprMVar(v___x_3032_, v___x_3033_, v___x_3034_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc_n(v_a_3036_, 2);
lean_dec_ref_known(v___x_3035_, 1);
v___x_3037_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_3038_ = lean_box(0);
v___x_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3039_, 0, v_a_3030_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3040_, 0, v_a_3028_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
lean_inc_ref(v___x_3040_);
v___x_3041_ = l_Lean_Expr_const___override(v___x_3037_, v___x_3040_);
lean_inc(v_a_3026_);
v___x_3042_ = l_Lean_mkAppB(v___x_3041_, v_a_3026_, v_a_3036_);
v___x_3043_ = lean_box(0);
v___x_3044_ = l_Lean_Meta_trySynthInstance(v___x_3042_, v___x_3043_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3131_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3131_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3131_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
if (lean_obj_tag(v_a_3045_) == 1)
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3127_; 
lean_del_object(v___x_3047_);
v_a_3049_ = lean_ctor_get(v_a_3045_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_a_3045_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3051_ = v_a_3045_;
v_isShared_3052_ = v_isSharedCheck_3127_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v_a_3045_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3127_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3053_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_3054_ = l_Lean_Expr_const___override(v___x_3053_, v___x_3040_);
lean_inc_ref(v_expr_3019_);
lean_inc(v_a_3049_);
v___x_3055_ = l_Lean_mkApp4(v___x_3054_, v_a_3026_, v_a_3036_, v_a_3049_, v_expr_3019_);
v___x_3056_ = l_Lean_Meta_expandCoe(v___x_3055_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3118_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3118_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3118_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v_fst_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3116_; 
v_fst_3061_ = lean_ctor_get(v_a_3057_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_a_3057_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v_a_3057_, 1);
lean_dec(v_unused_3117_);
v___x_3063_ = v_a_3057_;
v_isShared_3064_ = v_isSharedCheck_3116_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_fst_3061_);
lean_dec(v_a_3057_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3116_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3072_; 
lean_inc(v_a_3023_);
lean_inc_ref(v_a_3022_);
lean_inc(v_a_3021_);
lean_inc_ref(v_a_3020_);
lean_inc(v_fst_3061_);
v___x_3072_ = lean_infer_type(v_fst_3061_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3074_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
lean_inc(v_a_3023_);
lean_inc_ref(v_a_3022_);
lean_inc(v_a_3021_);
lean_inc_ref(v_a_3020_);
v___x_3074_ = lean_whnf(v_a_3073_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; uint8_t v___x_3076_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v___x_3074_, 1);
v___x_3076_ = l_Lean_Expr_isSort(v_a_3075_);
lean_dec(v_a_3075_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
lean_del_object(v___x_3059_);
lean_del_object(v___x_3051_);
v___x_3077_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3078_ = l_Lean_indentExpr(v_expr_3019_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 7);
lean_ctor_set(v___x_3063_, 1, v___x_3078_);
lean_ctor_set(v___x_3063_, 0, v___x_3077_);
v___x_3080_ = v___x_3063_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
v___x_3081_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = l_Lean_indentExpr(v_fst_3061_);
v___x_3084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3086_ = l_Lean_indentExpr(v_a_3049_);
v___x_3087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = l_Lean_MessageData_hint_x27(v___x_3087_);
v___x_3089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3084_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3089_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_del_object(v___x_3063_);
lean_dec(v_a_3049_);
lean_dec_ref(v_expr_3019_);
goto v___jp_3065_;
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_del_object(v___x_3063_);
lean_dec(v_fst_3061_);
lean_del_object(v___x_3059_);
lean_del_object(v___x_3051_);
lean_dec(v_a_3049_);
lean_dec_ref(v_expr_3019_);
v_a_3100_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3074_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3074_);
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
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_del_object(v___x_3063_);
lean_dec(v_fst_3061_);
lean_del_object(v___x_3059_);
lean_del_object(v___x_3051_);
lean_dec(v_a_3049_);
lean_dec_ref(v_expr_3019_);
v_a_3108_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3072_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3072_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
v___jp_3065_:
{
lean_object* v___x_3067_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v_fst_3061_);
v___x_3067_ = v___x_3051_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_fst_3061_);
v___x_3067_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
lean_object* v___x_3069_; 
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3067_);
v___x_3069_ = v___x_3059_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3067_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_del_object(v___x_3051_);
lean_dec(v_a_3049_);
lean_dec_ref(v_expr_3019_);
v_a_3119_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3056_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3056_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
else
{
lean_object* v___x_3129_; 
lean_dec(v_a_3045_);
lean_dec_ref_known(v___x_3040_, 2);
lean_dec(v_a_3036_);
lean_dec(v_a_3026_);
lean_dec_ref(v_expr_3019_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3043_);
v___x_3129_ = v___x_3047_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3043_);
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
lean_dec_ref_known(v___x_3040_, 2);
lean_dec(v_a_3036_);
lean_dec(v_a_3026_);
lean_dec_ref(v_expr_3019_);
v_a_3132_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3044_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3044_);
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
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_a_3030_);
lean_dec(v_a_3028_);
lean_dec(v_a_3026_);
lean_dec_ref(v_expr_3019_);
v_a_3140_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3035_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3035_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v_a_3028_);
lean_dec(v_a_3026_);
lean_dec_ref(v_expr_3019_);
v_a_3148_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3029_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3029_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
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
lean_dec(v_a_3026_);
lean_dec_ref(v_expr_3019_);
v_a_3156_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3027_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3027_);
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
lean_dec_ref(v_expr_3019_);
v_a_3164_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3025_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3025_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_);
lean_dec(v_a_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_a_3174_);
lean_dec_ref(v_a_3173_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3179_, lean_object* v___y_3180_){
_start:
{
uint8_t v___x_3182_; 
v___x_3182_ = l_Lean_Expr_hasMVar(v_e_3179_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; 
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v_e_3179_);
return v___x_3183_;
}
else
{
lean_object* v___x_3184_; lean_object* v_mctx_3185_; lean_object* v___x_3186_; lean_object* v_fst_3187_; lean_object* v_snd_3188_; lean_object* v___x_3189_; lean_object* v_cache_3190_; lean_object* v_zetaDeltaFVarIds_3191_; lean_object* v_postponed_3192_; lean_object* v_diag_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3202_; 
v___x_3184_ = lean_st_ref_get(v___y_3180_);
v_mctx_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc_ref(v_mctx_3185_);
lean_dec(v___x_3184_);
v___x_3186_ = l_Lean_instantiateMVarsCore(v_mctx_3185_, v_e_3179_);
v_fst_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_fst_3187_);
v_snd_3188_ = lean_ctor_get(v___x_3186_, 1);
lean_inc(v_snd_3188_);
lean_dec_ref(v___x_3186_);
v___x_3189_ = lean_st_ref_take(v___y_3180_);
v_cache_3190_ = lean_ctor_get(v___x_3189_, 1);
v_zetaDeltaFVarIds_3191_ = lean_ctor_get(v___x_3189_, 2);
v_postponed_3192_ = lean_ctor_get(v___x_3189_, 3);
v_diag_3193_ = lean_ctor_get(v___x_3189_, 4);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3202_ == 0)
{
lean_object* v_unused_3203_; 
v_unused_3203_ = lean_ctor_get(v___x_3189_, 0);
lean_dec(v_unused_3203_);
v___x_3195_ = v___x_3189_;
v_isShared_3196_ = v_isSharedCheck_3202_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_diag_3193_);
lean_inc(v_postponed_3192_);
lean_inc(v_zetaDeltaFVarIds_3191_);
lean_inc(v_cache_3190_);
lean_dec(v___x_3189_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3202_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v_snd_3188_);
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_snd_3188_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_cache_3190_);
lean_ctor_set(v_reuseFailAlloc_3201_, 2, v_zetaDeltaFVarIds_3191_);
lean_ctor_set(v_reuseFailAlloc_3201_, 3, v_postponed_3192_);
lean_ctor_set(v_reuseFailAlloc_3201_, 4, v_diag_3193_);
v___x_3198_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = lean_st_ref_put(v___y_3180_, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v_fst_3187_);
return v___x_3200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3204_, v___y_3205_);
lean_dec(v___y_3205_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3208_, v___y_3210_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v___y_3229_; lean_object* v___x_3268_; uint8_t v_transparency_3269_; uint8_t v___x_3270_; uint8_t v___x_3271_; 
v___x_3268_ = l_Lean_Meta_Context_config(v_a_3223_);
v_transparency_3269_ = lean_ctor_get_uint8(v___x_3268_, 9);
lean_dec_ref(v___x_3268_);
v___x_3270_ = 2;
v___x_3271_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3269_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v_keyedConfig_3272_; uint8_t v_trackZetaDelta_3273_; lean_object* v_zetaDeltaSet_3274_; lean_object* v_lctx_3275_; lean_object* v_localInstances_3276_; lean_object* v_defEqCtx_x3f_3277_; lean_object* v_synthPendingDepth_3278_; lean_object* v_customCanUnfoldPredicate_x3f_3279_; uint8_t v_univApprox_3280_; uint8_t v_inTypeClassResolution_3281_; uint8_t v_cacheInferType_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_keyedConfig_3272_ = lean_ctor_get(v_a_3223_, 0);
v_trackZetaDelta_3273_ = lean_ctor_get_uint8(v_a_3223_, sizeof(void*)*7);
v_zetaDeltaSet_3274_ = lean_ctor_get(v_a_3223_, 1);
v_lctx_3275_ = lean_ctor_get(v_a_3223_, 2);
v_localInstances_3276_ = lean_ctor_get(v_a_3223_, 3);
v_defEqCtx_x3f_3277_ = lean_ctor_get(v_a_3223_, 4);
v_synthPendingDepth_3278_ = lean_ctor_get(v_a_3223_, 5);
v_customCanUnfoldPredicate_x3f_3279_ = lean_ctor_get(v_a_3223_, 6);
v_univApprox_3280_ = lean_ctor_get_uint8(v_a_3223_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3281_ = lean_ctor_get_uint8(v_a_3223_, sizeof(void*)*7 + 2);
v_cacheInferType_3282_ = lean_ctor_get_uint8(v_a_3223_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3272_);
v___x_3283_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3270_, v_keyedConfig_3272_);
lean_inc(v_customCanUnfoldPredicate_x3f_3279_);
lean_inc(v_synthPendingDepth_3278_);
lean_inc(v_defEqCtx_x3f_3277_);
lean_inc_ref(v_localInstances_3276_);
lean_inc_ref(v_lctx_3275_);
lean_inc(v_zetaDeltaSet_3274_);
v___x_3284_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
lean_ctor_set(v___x_3284_, 1, v_zetaDeltaSet_3274_);
lean_ctor_set(v___x_3284_, 2, v_lctx_3275_);
lean_ctor_set(v___x_3284_, 3, v_localInstances_3276_);
lean_ctor_set(v___x_3284_, 4, v_defEqCtx_x3f_3277_);
lean_ctor_set(v___x_3284_, 5, v_synthPendingDepth_3278_);
lean_ctor_set(v___x_3284_, 6, v_customCanUnfoldPredicate_x3f_3279_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*7, v_trackZetaDelta_3273_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*7 + 1, v_univApprox_3280_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3281_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*7 + 3, v_cacheInferType_3282_);
lean_inc(v_a_3226_);
lean_inc_ref(v_a_3225_);
lean_inc(v_a_3224_);
v___x_3285_ = lean_whnf(v_type_3222_, v___x_3284_, v_a_3224_, v_a_3225_, v_a_3226_);
v___y_3229_ = v___x_3285_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3286_; 
lean_inc(v_a_3226_);
lean_inc_ref(v_a_3225_);
lean_inc(v_a_3224_);
lean_inc_ref(v_a_3223_);
v___x_3286_ = lean_whnf(v_type_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
v___y_3229_ = v___x_3286_;
goto v___jp_3228_;
}
v___jp_3228_:
{
if (lean_obj_tag(v___y_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3259_; 
v_a_3230_ = lean_ctor_get(v___y_3229_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___y_3229_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3232_ = v___y_3229_;
v_isShared_3233_ = v_isSharedCheck_3259_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___y_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3259_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
if (lean_obj_tag(v_a_3230_) == 5)
{
lean_object* v_fn_3234_; lean_object* v_arg_3235_; lean_object* v___x_3236_; lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3254_; 
lean_del_object(v___x_3232_);
v_fn_3234_ = lean_ctor_get(v_a_3230_, 0);
lean_inc_ref(v_fn_3234_);
v_arg_3235_ = lean_ctor_get(v_a_3230_, 1);
lean_inc_ref(v_arg_3235_);
lean_dec_ref_known(v_a_3230_, 2);
v___x_3236_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3234_, v_a_3224_);
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3254_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3254_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3253_; 
v___x_3241_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3235_, v_a_3224_);
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3253_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3253_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v_a_3237_);
lean_ctor_set(v___x_3246_, 1, v_a_3242_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 1);
lean_ctor_set(v___x_3239_, 0, v___x_3246_);
v___x_3248_ = v___x_3239_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3250_; 
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3248_);
v___x_3250_ = v___x_3244_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
else
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
lean_dec(v_a_3230_);
v___x_3255_ = lean_box(0);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3255_);
v___x_3257_ = v___x_3232_;
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
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
v_a_3260_ = lean_ctor_get(v___y_3229_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___y_3229_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___y_3229_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___y_3229_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_Meta_isTypeApp_x3f(v_type_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Lean_Meta_isTypeApp_x3f(v_type_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3336_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3336_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3336_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
if (lean_obj_tag(v_a_3301_) == 1)
{
lean_object* v_val_3305_; lean_object* v_fst_3306_; lean_object* v___x_3307_; 
lean_del_object(v___x_3303_);
v_val_3305_ = lean_ctor_get(v_a_3301_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v_a_3301_, 1);
v_fst_3306_ = lean_ctor_get(v_val_3305_, 0);
lean_inc(v_fst_3306_);
lean_dec(v_val_3305_);
v___x_3307_ = l_Lean_Meta_isMonad_x3f(v_fst_3306_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3322_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3322_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3322_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
if (lean_obj_tag(v_a_3308_) == 0)
{
uint8_t v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3312_ = 0;
v___x_3313_ = lean_box(v___x_3312_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3313_);
v___x_3315_ = v___x_3310_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
else
{
uint8_t v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
lean_dec_ref_known(v_a_3308_, 1);
v___x_3317_ = 1;
v___x_3318_ = lean_box(v___x_3317_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3318_);
v___x_3320_ = v___x_3310_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
v_a_3323_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3307_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3307_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
else
{
uint8_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
lean_dec(v_a_3301_);
v___x_3331_ = 0;
v___x_3332_ = lean_box(v___x_3331_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3332_);
v___x_3334_ = v___x_3303_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
v_a_3337_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3300_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3300_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lean_Meta_isMonadApp(v_type_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
lean_dec(v_a_3349_);
lean_dec_ref(v_a_3348_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
return v_res_3351_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3352_, lean_object* v_opt_3353_){
_start:
{
lean_object* v_name_3354_; lean_object* v_defValue_3355_; lean_object* v_map_3356_; lean_object* v___x_3357_; 
v_name_3354_ = lean_ctor_get(v_opt_3353_, 0);
v_defValue_3355_ = lean_ctor_get(v_opt_3353_, 1);
v_map_3356_ = lean_ctor_get(v_opts_3352_, 0);
v___x_3357_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3356_, v_name_3354_);
if (lean_obj_tag(v___x_3357_) == 0)
{
uint8_t v___x_3358_; 
v___x_3358_ = lean_unbox(v_defValue_3355_);
return v___x_3358_;
}
else
{
lean_object* v_val_3359_; 
v_val_3359_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v___x_3357_, 1);
if (lean_obj_tag(v_val_3359_) == 1)
{
uint8_t v_v_3360_; 
v_v_3360_ = lean_ctor_get_uint8(v_val_3359_, 0);
lean_dec_ref_known(v_val_3359_, 0);
return v_v_3360_;
}
else
{
uint8_t v___x_3361_; 
lean_dec(v_val_3359_);
v___x_3361_ = lean_unbox(v_defValue_3355_);
return v___x_3361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3362_, lean_object* v_opt_3363_){
_start:
{
uint8_t v_res_3364_; lean_object* v_r_3365_; 
v_res_3364_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3362_, v_opt_3363_);
lean_dec_ref(v_opt_3363_);
lean_dec_ref(v_opts_3362_);
v_r_3365_ = lean_box(v_res_3364_);
return v_r_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec_ref(v_x_3376_);
return v_res_3382_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = lean_unsigned_to_nat(0u);
v___x_3393_ = l_Lean_mkBVar(v___x_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3405_, lean_object* v_expectedType_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v_a_3413_; lean_object* v___y_3421_; lean_object* v___x_3431_; lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3835_; 
v___x_3431_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3406_, v_a_3408_);
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3835_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3835_;
goto v_resetjp_3433_;
}
v___jp_3412_:
{
uint8_t v___x_3414_; 
v___x_3414_ = l_Lean_Exception_isInterrupt(v_a_3413_);
if (v___x_3414_ == 0)
{
uint8_t v___x_3415_; 
lean_inc_ref(v_a_3413_);
v___x_3415_ = l_Lean_Exception_isRuntime(v_a_3413_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec_ref(v_a_3413_);
v___x_3416_ = lean_box(0);
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
return v___x_3417_;
}
else
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3418_, 0, v_a_3413_);
return v___x_3418_;
}
}
else
{
lean_object* v___x_3419_; 
v___x_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3419_, 0, v_a_3413_);
return v___x_3419_;
}
}
v___jp_3420_:
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3430_; 
v_a_3422_ = lean_ctor_get(v___y_3421_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___y_3421_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3424_ = v___y_3421_;
v_isShared_3425_ = v_isSharedCheck_3430_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___y_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3430_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_a_3426_; lean_object* v___x_3428_; 
v_a_3426_ = lean_ctor_get(v_a_3422_, 0);
lean_inc(v_a_3426_);
lean_dec(v_a_3422_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v_a_3426_);
v___x_3428_ = v___x_3424_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; 
lean_inc(v_a_3410_);
lean_inc_ref(v_a_3409_);
lean_inc(v_a_3408_);
lean_inc_ref(v_a_3407_);
lean_inc_ref(v_e_3405_);
v___x_3436_ = lean_infer_type(v_e_3405_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3438_; lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3826_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3436_, 1);
v___x_3438_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3437_, v_a_3408_);
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3441_ = v___x_3438_;
v_isShared_3442_ = v_isSharedCheck_3826_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3826_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; 
lean_inc(v_a_3432_);
v___x_3443_ = l_Lean_Meta_isTypeApp_x3f(v_a_3432_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3817_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3446_ = v___x_3443_;
v_isShared_3447_ = v_isSharedCheck_3817_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3817_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
if (lean_obj_tag(v_a_3444_) == 1)
{
lean_object* v_val_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3812_; 
lean_del_object(v___x_3446_);
v_val_3448_ = lean_ctor_get(v_a_3444_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_a_3444_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3450_ = v_a_3444_;
v_isShared_3451_ = v_isSharedCheck_3812_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_val_3448_);
lean_dec(v_a_3444_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3812_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_fst_3452_; lean_object* v_snd_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3811_; 
v_fst_3452_ = lean_ctor_get(v_val_3448_, 0);
v_snd_3453_ = lean_ctor_get(v_val_3448_, 1);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_val_3448_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3455_ = v_val_3448_;
v_isShared_3456_ = v_isSharedCheck_3811_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_snd_3453_);
lean_inc(v_fst_3452_);
lean_dec(v_val_3448_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3811_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; 
lean_inc(v_a_3439_);
v___x_3457_ = l_Lean_Meta_isTypeApp_x3f(v_a_3439_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3802_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3460_ = v___x_3457_;
v_isShared_3461_ = v_isSharedCheck_3802_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3802_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
if (lean_obj_tag(v_a_3458_) == 1)
{
lean_object* v_val_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3797_; 
lean_del_object(v___x_3460_);
v_val_3462_ = lean_ctor_get(v_a_3458_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_a_3458_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3464_ = v_a_3458_;
v_isShared_3465_ = v_isSharedCheck_3797_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_val_3462_);
lean_dec(v_a_3458_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3797_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_fst_3466_; lean_object* v_snd_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3796_; 
v_fst_3466_ = lean_ctor_get(v_val_3462_, 0);
v_snd_3467_ = lean_ctor_get(v_val_3462_, 1);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_val_3462_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3469_ = v_val_3462_;
v_isShared_3470_ = v_isSharedCheck_3796_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_snd_3467_);
lean_inc(v_fst_3466_);
lean_dec(v_val_3462_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3796_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_Meta_saveState___redArg(v_a_3408_, v_a_3410_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3473_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
lean_inc(v_fst_3452_);
lean_inc(v_fst_3466_);
v___x_3473_ = l_Lean_Meta_isExprDefEq(v_fst_3466_, v_fst_3452_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3779_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3779_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3779_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_unbox(v_a_3474_);
lean_dec(v_a_3474_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
lean_dec(v_a_3472_);
lean_del_object(v___x_3450_);
lean_del_object(v___x_3441_);
lean_del_object(v___x_3434_);
v___x_3479_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3409_);
v___x_3480_ = l_Lean_Meta_autoLift;
v___x_3481_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v___x_3479_, v___x_3480_);
lean_dec_ref(v___x_3479_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3484_; 
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v___x_3482_ = lean_box(0);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3482_);
v___x_3484_ = v___x_3476_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
else
{
lean_object* v___x_3486_; 
lean_del_object(v___x_3476_);
lean_inc(v_a_3410_);
lean_inc_ref(v_a_3409_);
lean_inc(v_a_3408_);
lean_inc_ref(v_a_3407_);
lean_inc(v_fst_3466_);
v___x_3486_ = lean_infer_type(v_fst_3466_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
lean_inc(v_a_3410_);
lean_inc_ref(v_a_3409_);
lean_inc(v_a_3408_);
lean_inc_ref(v_a_3407_);
v___x_3488_ = lean_whnf(v_a_3487_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
if (lean_obj_tag(v_a_3489_) == 7)
{
lean_object* v_binderType_3490_; 
v_binderType_3490_ = lean_ctor_get(v_a_3489_, 1);
if (lean_obj_tag(v_binderType_3490_) == 3)
{
lean_object* v_body_3491_; 
v_body_3491_ = lean_ctor_get(v_a_3489_, 2);
if (lean_obj_tag(v_body_3491_) == 3)
{
lean_object* v_u_3492_; lean_object* v_u_3493_; lean_object* v___x_3494_; 
lean_inc_ref(v_body_3491_);
lean_inc_ref(v_binderType_3490_);
lean_dec_ref_known(v_a_3489_, 3);
v_u_3492_ = lean_ctor_get(v_binderType_3490_, 0);
lean_inc(v_u_3492_);
lean_dec_ref_known(v_binderType_3490_, 1);
v_u_3493_ = lean_ctor_get(v_body_3491_, 0);
lean_inc(v_u_3493_);
lean_dec_ref_known(v_body_3491_, 1);
lean_inc(v_a_3410_);
lean_inc_ref(v_a_3409_);
lean_inc(v_a_3408_);
lean_inc_ref(v_a_3407_);
lean_inc(v_fst_3452_);
v___x_3494_ = lean_infer_type(v_fst_3452_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3496_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
lean_inc(v_a_3410_);
lean_inc_ref(v_a_3409_);
lean_inc(v_a_3408_);
lean_inc_ref(v_a_3407_);
v___x_3496_ = lean_whnf(v_a_3495_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
if (lean_obj_tag(v_a_3497_) == 7)
{
lean_object* v_binderType_3498_; 
v_binderType_3498_ = lean_ctor_get(v_a_3497_, 1);
if (lean_obj_tag(v_binderType_3498_) == 3)
{
lean_object* v_body_3499_; 
v_body_3499_ = lean_ctor_get(v_a_3497_, 2);
if (lean_obj_tag(v_body_3499_) == 3)
{
lean_object* v_u_3500_; lean_object* v_u_3501_; lean_object* v___x_3502_; 
lean_inc_ref(v_body_3499_);
lean_inc_ref(v_binderType_3498_);
lean_dec_ref_known(v_a_3497_, 3);
v_u_3500_ = lean_ctor_get(v_binderType_3498_, 0);
lean_inc(v_u_3500_);
lean_dec_ref_known(v_binderType_3498_, 1);
v_u_3501_ = lean_ctor_get(v_body_3499_, 0);
lean_inc(v_u_3501_);
lean_dec_ref_known(v_body_3499_, 1);
v___x_3502_ = l_Lean_Meta_decLevel(v_u_3492_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3504_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v___x_3504_ = l_Lean_Meta_decLevel(v_u_3500_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___x_3506_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3504_, 1);
lean_inc(v_a_3503_);
v___x_3506_ = l_Lean_Meta_isLevelDefEq(v_a_3503_, v_a_3505_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3671_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3671_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3671_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
uint8_t v___x_3511_; 
v___x_3511_ = lean_unbox(v_a_3507_);
lean_dec(v_a_3507_);
if (v___x_3511_ == 1)
{
lean_object* v___x_3512_; 
lean_del_object(v___x_3509_);
v___x_3512_ = l_Lean_Meta_decLevel(v_u_3493_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3514_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v___x_3514_ = l_Lean_Meta_decLevel(v_u_3501_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___x_3516_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3517_ = lean_box(0);
if (v_isShared_3470_ == 0)
{
lean_ctor_set_tag(v___x_3469_, 1);
lean_ctor_set(v___x_3469_, 1, v___x_3517_);
lean_ctor_set(v___x_3469_, 0, v_a_3515_);
v___x_3519_ = v___x_3469_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3515_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
if (v_isShared_3456_ == 0)
{
lean_ctor_set_tag(v___x_3455_, 1);
lean_ctor_set(v___x_3455_, 1, v___x_3519_);
lean_ctor_set(v___x_3455_, 0, v_a_3513_);
v___x_3521_ = v___x_3455_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3513_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v___x_3519_);
v___x_3521_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_a_3503_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l_Lean_Expr_const___override(v___x_3516_, v___x_3522_);
v___x_3524_ = lean_unsigned_to_nat(2u);
v___x_3525_ = lean_mk_empty_array_with_capacity(v___x_3524_);
lean_inc(v_fst_3466_);
v___x_3526_ = lean_array_push(v___x_3525_, v_fst_3466_);
lean_inc(v_fst_3452_);
v___x_3527_ = lean_array_push(v___x_3526_, v_fst_3452_);
v___x_3528_ = l_Lean_mkAppN(v___x_3523_, v___x_3527_);
lean_dec_ref(v___x_3527_);
v___x_3529_ = lean_box(0);
v___x_3530_ = l_Lean_Meta_trySynthInstance(v___x_3528_, v___x_3529_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3661_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3661_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3661_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
if (lean_obj_tag(v_a_3531_) == 1)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; 
lean_del_object(v___x_3533_);
v_a_3535_ = lean_ctor_get(v_a_3531_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v_a_3531_, 1);
lean_inc(v_snd_3467_);
v___x_3536_ = l_Lean_Meta_getDecLevel(v_snd_3467_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = l_Lean_Meta_getDecLevel(v_a_3439_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3540_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref_known(v___x_3538_, 1);
lean_inc(v_a_3432_);
v___x_3540_ = l_Lean_Meta_getDecLevel(v_a_3432_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3540_, 1);
v___x_3542_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3543_, 0, v_a_3541_);
lean_ctor_set(v___x_3543_, 1, v___x_3517_);
v___x_3544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3544_, 0, v_a_3539_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3545_, 0, v_a_3537_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
lean_inc_ref(v___x_3545_);
v___x_3546_ = l_Lean_mkConst(v___x_3542_, v___x_3545_);
v___x_3547_ = lean_unsigned_to_nat(5u);
v___x_3548_ = lean_mk_empty_array_with_capacity(v___x_3547_);
lean_inc(v_fst_3466_);
v___x_3549_ = lean_array_push(v___x_3548_, v_fst_3466_);
lean_inc(v_fst_3452_);
v___x_3550_ = lean_array_push(v___x_3549_, v_fst_3452_);
lean_inc(v_a_3535_);
v___x_3551_ = lean_array_push(v___x_3550_, v_a_3535_);
lean_inc(v_snd_3467_);
v___x_3552_ = lean_array_push(v___x_3551_, v_snd_3467_);
lean_inc_ref(v_e_3405_);
v___x_3553_ = lean_array_push(v___x_3552_, v_e_3405_);
v___x_3554_ = l_Lean_mkAppN(v___x_3546_, v___x_3553_);
lean_dec_ref(v___x_3553_);
lean_inc(v_a_3410_);
lean_inc_ref(v_a_3409_);
lean_inc(v_a_3408_);
lean_inc_ref(v_a_3407_);
lean_inc_ref(v___x_3554_);
v___x_3555_ = lean_infer_type(v___x_3554_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3555_, 1);
lean_inc(v_a_3432_);
v___x_3557_ = l_Lean_Meta_isExprDefEq(v_a_3432_, v_a_3556_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3652_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3560_ = v___x_3557_;
v_isShared_3561_ = v_isSharedCheck_3652_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3557_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3652_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
uint8_t v___x_3562_; 
v___x_3562_ = lean_unbox(v_a_3558_);
lean_dec(v_a_3558_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; 
lean_del_object(v___x_3560_);
lean_dec_ref(v___x_3554_);
lean_del_object(v___x_3464_);
lean_inc(v_fst_3452_);
v___x_3563_ = l_Lean_Meta_isMonad_x3f(v_fst_3452_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3644_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3566_ = v___x_3563_;
v_isShared_3567_ = v_isSharedCheck_3644_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3563_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3644_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
if (lean_obj_tag(v_a_3564_) == 1)
{
lean_object* v_val_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3640_; 
lean_del_object(v___x_3566_);
v_val_3568_ = lean_ctor_get(v_a_3564_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_a_3564_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3570_ = v_a_3564_;
v_isShared_3571_ = v_isSharedCheck_3640_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_val_3568_);
lean_dec(v_a_3564_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3640_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; 
lean_inc(v_snd_3467_);
v___x_3572_ = l_Lean_Meta_getLevel(v_snd_3467_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3574_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v___x_3572_, 1);
lean_inc(v_snd_3453_);
v___x_3574_ = l_Lean_Meta_getLevel(v_snd_3453_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3574_, 1);
v___x_3576_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3577_ = 0;
v___x_3578_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3579_, 0, v_a_3575_);
lean_ctor_set(v___x_3579_, 1, v___x_3517_);
v___x_3580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3580_, 0, v_a_3573_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = l_Lean_mkConst(v___x_3578_, v___x_3580_);
v___x_3582_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3583_ = lean_unsigned_to_nat(3u);
v___x_3584_ = lean_mk_empty_array_with_capacity(v___x_3583_);
lean_inc_n(v_snd_3467_, 2);
v___x_3585_ = lean_array_push(v___x_3584_, v_snd_3467_);
v___x_3586_ = lean_array_push(v___x_3585_, v___x_3582_);
lean_inc(v_snd_3453_);
v___x_3587_ = lean_array_push(v___x_3586_, v_snd_3453_);
v___x_3588_ = l_Lean_mkAppN(v___x_3581_, v___x_3587_);
lean_dec_ref(v___x_3587_);
v___x_3589_ = l_Lean_mkForall(v___x_3576_, v___x_3577_, v_snd_3467_, v___x_3588_);
v___x_3590_ = l_Lean_Meta_trySynthInstance(v___x_3589_, v___x_3529_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3636_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3636_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3636_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
if (lean_obj_tag(v_a_3591_) == 1)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
lean_del_object(v___x_3593_);
v_a_3595_ = lean_ctor_get(v_a_3591_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v_a_3591_, 1);
v___x_3596_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3597_ = l_Lean_mkConst(v___x_3596_, v___x_3545_);
v___x_3598_ = lean_unsigned_to_nat(8u);
v___x_3599_ = lean_mk_empty_array_with_capacity(v___x_3598_);
v___x_3600_ = lean_array_push(v___x_3599_, v_fst_3466_);
v___x_3601_ = lean_array_push(v___x_3600_, v_fst_3452_);
v___x_3602_ = lean_array_push(v___x_3601_, v_snd_3467_);
v___x_3603_ = lean_array_push(v___x_3602_, v_snd_3453_);
v___x_3604_ = lean_array_push(v___x_3603_, v_a_3535_);
v___x_3605_ = lean_array_push(v___x_3604_, v_a_3595_);
v___x_3606_ = lean_array_push(v___x_3605_, v_val_3568_);
v___x_3607_ = lean_array_push(v___x_3606_, v_e_3405_);
v___x_3608_ = l_Lean_mkAppN(v___x_3597_, v___x_3607_);
lean_dec_ref(v___x_3607_);
v___x_3609_ = l_Lean_Meta_expandCoe(v___x_3608_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v_fst_3611_; lean_object* v___x_3612_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
v_fst_3611_ = lean_ctor_get(v_a_3610_, 0);
lean_inc_n(v_fst_3611_, 2);
lean_dec(v_a_3610_);
lean_inc(v_a_3410_);
lean_inc_ref(v_a_3409_);
lean_inc(v_a_3408_);
lean_inc_ref(v_a_3407_);
v___x_3612_ = lean_infer_type(v_fst_3611_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3614_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
v___x_3614_ = l_Lean_Meta_isExprDefEq(v_a_3432_, v_a_3613_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3629_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3629_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3629_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
uint8_t v___x_3619_; 
v___x_3619_ = lean_unbox(v_a_3615_);
lean_dec(v_a_3615_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3621_; 
lean_dec(v_fst_3611_);
lean_del_object(v___x_3570_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 0, v___x_3529_);
v___x_3621_ = v___x_3617_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3529_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
else
{
lean_object* v___x_3624_; 
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v_fst_3611_);
v___x_3624_ = v___x_3570_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_fst_3611_);
v___x_3624_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3626_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 0, v___x_3624_);
v___x_3626_ = v___x_3617_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
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
}
else
{
lean_object* v_a_3630_; 
lean_dec(v_fst_3611_);
lean_del_object(v___x_3570_);
v_a_3630_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3614_, 1);
v_a_3413_ = v_a_3630_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3631_; 
lean_dec(v_fst_3611_);
lean_del_object(v___x_3570_);
lean_dec(v_a_3432_);
v_a_3631_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3612_, 1);
v_a_3413_ = v_a_3631_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3632_; 
lean_del_object(v___x_3570_);
lean_dec(v_a_3432_);
v_a_3632_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___x_3609_, 1);
v_a_3413_ = v_a_3632_;
goto v___jp_3412_;
}
}
else
{
lean_object* v___x_3634_; 
lean_dec(v_a_3591_);
lean_del_object(v___x_3570_);
lean_dec(v_val_3568_);
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v___x_3529_);
v___x_3634_ = v___x_3593_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3529_);
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
lean_del_object(v___x_3570_);
lean_dec(v_val_3568_);
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3637_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3590_, 1);
v_a_3413_ = v_a_3637_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3638_; 
lean_dec(v_a_3573_);
lean_del_object(v___x_3570_);
lean_dec(v_val_3568_);
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3638_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3574_, 1);
v_a_3413_ = v_a_3638_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3639_; 
lean_del_object(v___x_3570_);
lean_dec(v_val_3568_);
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3639_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3572_, 1);
v_a_3413_ = v_a_3639_;
goto v___jp_3412_;
}
}
}
else
{
lean_object* v___x_3642_; 
lean_dec(v_a_3564_);
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3529_);
v___x_3642_ = v___x_3566_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3529_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
else
{
lean_object* v_a_3645_; 
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3645_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3563_, 1);
v_a_3413_ = v_a_3645_;
goto v___jp_3412_;
}
}
else
{
lean_object* v___x_3647_; 
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3554_);
v___x_3647_ = v___x_3464_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3554_);
v___x_3647_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3649_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3647_);
v___x_3649_ = v___x_3560_;
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
lean_dec_ref(v___x_3554_);
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3653_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3557_, 1);
v_a_3413_ = v_a_3653_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3654_; 
lean_dec_ref(v___x_3554_);
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3654_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3555_, 1);
v_a_3413_ = v_a_3654_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3655_; 
lean_dec(v_a_3539_);
lean_dec(v_a_3537_);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3655_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3540_, 1);
v_a_3413_ = v_a_3655_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3656_; 
lean_dec(v_a_3537_);
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3656_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3538_, 1);
v_a_3413_ = v_a_3656_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3657_; 
lean_dec(v_a_3535_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3657_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v___x_3536_, 1);
v_a_3413_ = v_a_3657_;
goto v___jp_3412_;
}
}
else
{
lean_object* v___x_3659_; 
lean_dec(v_a_3531_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3529_);
v___x_3659_ = v___x_3533_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3529_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
else
{
lean_object* v_a_3662_; 
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3662_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3530_, 1);
v_a_3413_ = v_a_3662_;
goto v___jp_3412_;
}
}
}
}
else
{
lean_object* v_a_3665_; 
lean_dec(v_a_3513_);
lean_dec(v_a_3503_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3665_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3514_, 1);
v_a_3413_ = v_a_3665_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3666_; 
lean_dec(v_a_3503_);
lean_dec(v_u_3501_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3666_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3512_, 1);
v_a_3413_ = v_a_3666_;
goto v___jp_3412_;
}
}
else
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
lean_dec(v_a_3503_);
lean_dec(v_u_3501_);
lean_dec(v_u_3493_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v___x_3667_ = lean_box(0);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3667_);
v___x_3669_ = v___x_3509_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v_a_3672_; 
lean_dec(v_a_3503_);
lean_dec(v_u_3501_);
lean_dec(v_u_3493_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3672_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3506_, 1);
v_a_3413_ = v_a_3672_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3673_; 
lean_dec(v_a_3503_);
lean_dec(v_u_3501_);
lean_dec(v_u_3493_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3673_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3504_, 1);
v_a_3413_ = v_a_3673_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3674_; 
lean_dec(v_u_3501_);
lean_dec(v_u_3500_);
lean_dec(v_u_3493_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3674_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3674_);
lean_dec_ref_known(v___x_3502_, 1);
v_a_3413_ = v_a_3674_;
goto v___jp_3412_;
}
}
else
{
lean_object* v___x_3675_; 
lean_dec(v_u_3493_);
lean_dec(v_u_3492_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v___x_3675_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3497_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
lean_dec_ref_known(v_a_3497_, 3);
v___y_3421_ = v___x_3675_;
goto v___jp_3420_;
}
}
else
{
lean_object* v___x_3676_; 
lean_dec(v_u_3493_);
lean_dec(v_u_3492_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v___x_3676_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3497_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
lean_dec_ref_known(v_a_3497_, 3);
v___y_3421_ = v___x_3676_;
goto v___jp_3420_;
}
}
else
{
lean_object* v___x_3677_; 
lean_dec(v_u_3493_);
lean_dec(v_u_3492_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v___x_3677_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3497_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
lean_dec(v_a_3497_);
v___y_3421_ = v___x_3677_;
goto v___jp_3420_;
}
}
else
{
lean_object* v_a_3678_; 
lean_dec(v_u_3493_);
lean_dec(v_u_3492_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3678_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3496_, 1);
v_a_3413_ = v_a_3678_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3679_; 
lean_dec(v_u_3493_);
lean_dec(v_u_3492_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3679_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3494_, 1);
v_a_3413_ = v_a_3679_;
goto v___jp_3412_;
}
}
else
{
lean_object* v___x_3680_; 
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v___x_3680_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3489_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
lean_dec_ref_known(v_a_3489_, 3);
v___y_3421_ = v___x_3680_;
goto v___jp_3420_;
}
}
else
{
lean_object* v___x_3681_; 
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v___x_3681_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3489_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
lean_dec_ref_known(v_a_3489_, 3);
v___y_3421_ = v___x_3681_;
goto v___jp_3420_;
}
}
else
{
lean_object* v___x_3682_; 
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v___x_3682_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3489_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
lean_dec(v_a_3489_);
v___y_3421_ = v___x_3682_;
goto v___jp_3420_;
}
}
else
{
lean_object* v_a_3683_; 
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3683_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3488_, 1);
v_a_3413_ = v_a_3683_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3684_; 
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3684_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3486_, 1);
v_a_3413_ = v_a_3684_;
goto v___jp_3412_;
}
}
}
else
{
lean_object* v___x_3685_; 
lean_del_object(v___x_3476_);
lean_del_object(v___x_3469_);
lean_del_object(v___x_3455_);
lean_dec(v_a_3439_);
lean_dec(v_a_3432_);
v___x_3685_ = l_Lean_Meta_isMonad_x3f(v_fst_3452_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3778_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3688_ = v___x_3685_;
v_isShared_3689_ = v_isSharedCheck_3778_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3685_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3778_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
if (lean_obj_tag(v_a_3686_) == 1)
{
lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3690_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v_fst_3466_);
v___x_3692_ = v___x_3464_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_fst_3466_);
v___x_3692_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3694_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v_snd_3467_);
v___x_3694_ = v___x_3450_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_snd_3467_);
v___x_3694_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3696_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set_tag(v___x_3441_, 1);
lean_ctor_set(v___x_3441_, 0, v_snd_3453_);
v___x_3696_ = v___x_3441_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_snd_3453_);
v___x_3696_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3697_; lean_object* v_a_3699_; lean_object* v___x_3726_; 
v___x_3697_ = lean_box(0);
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 1);
lean_ctor_set(v___x_3434_, 0, v_e_3405_);
v___x_3726_ = v___x_3434_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_e_3405_);
v___x_3726_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3725_;
}
v___jp_3698_:
{
uint8_t v___x_3700_; 
v___x_3700_ = l_Lean_Exception_isInterrupt(v_a_3699_);
if (v___x_3700_ == 0)
{
uint8_t v___x_3701_; 
lean_inc_ref(v_a_3699_);
v___x_3701_ = l_Lean_Exception_isRuntime(v_a_3699_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; 
lean_dec_ref(v_a_3699_);
lean_del_object(v___x_3688_);
v___x_3702_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3472_, v_a_3408_, v_a_3410_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v___x_3702_, 0);
lean_dec(v_unused_3710_);
v___x_3704_ = v___x_3702_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_dec(v___x_3702_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3697_);
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3697_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
v_a_3711_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3702_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3702_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
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
lean_object* v___x_3720_; 
lean_dec(v_a_3472_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set_tag(v___x_3688_, 1);
lean_ctor_set(v___x_3688_, 0, v_a_3699_);
v___x_3720_ = v___x_3688_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3699_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
else
{
lean_object* v___x_3723_; 
lean_dec(v_a_3472_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set_tag(v___x_3688_, 1);
lean_ctor_set(v___x_3688_, 0, v_a_3699_);
v___x_3723_ = v___x_3688_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3699_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
v_reusejp_3725_:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3727_ = lean_unsigned_to_nat(6u);
v___x_3728_ = lean_mk_empty_array_with_capacity(v___x_3727_);
v___x_3729_ = lean_array_push(v___x_3728_, v___x_3692_);
v___x_3730_ = lean_array_push(v___x_3729_, v___x_3694_);
v___x_3731_ = lean_array_push(v___x_3730_, v___x_3696_);
v___x_3732_ = lean_array_push(v___x_3731_, v___x_3697_);
v___x_3733_ = lean_array_push(v___x_3732_, v_a_3686_);
v___x_3734_ = lean_array_push(v___x_3733_, v___x_3726_);
v___x_3735_ = l_Lean_Meta_mkAppOptM(v___x_3690_, v___x_3734_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3754_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3738_ = v___x_3735_;
v_isShared_3739_ = v_isSharedCheck_3754_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3735_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3754_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Meta_expandCoe(v_a_3736_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3752_; 
lean_del_object(v___x_3688_);
lean_dec(v_a_3472_);
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3743_ = v___x_3740_;
v_isShared_3744_ = v_isSharedCheck_3752_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3740_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3752_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v_fst_3745_; lean_object* v___x_3747_; 
v_fst_3745_ = lean_ctor_get(v_a_3741_, 0);
lean_inc(v_fst_3745_);
lean_dec(v_a_3741_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set_tag(v___x_3738_, 1);
lean_ctor_set(v___x_3738_, 0, v_fst_3745_);
v___x_3747_ = v___x_3738_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_fst_3745_);
v___x_3747_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3749_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v___x_3747_);
v___x_3749_ = v___x_3743_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
lean_object* v_a_3753_; 
lean_del_object(v___x_3738_);
v_a_3753_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3740_, 1);
v_a_3699_ = v_a_3753_;
goto v___jp_3698_;
}
}
}
else
{
lean_object* v_a_3755_; 
v_a_3755_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3735_, 1);
v_a_3699_ = v_a_3755_;
goto v___jp_3698_;
}
}
}
}
}
}
else
{
lean_object* v___x_3760_; 
lean_del_object(v___x_3688_);
lean_dec(v_a_3686_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3453_);
lean_del_object(v___x_3450_);
lean_del_object(v___x_3441_);
lean_del_object(v___x_3434_);
lean_dec_ref(v_e_3405_);
v___x_3760_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3472_, v_a_3408_, v_a_3410_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3768_; 
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3768_ == 0)
{
lean_object* v_unused_3769_; 
v_unused_3769_ = lean_ctor_get(v___x_3760_, 0);
lean_dec(v_unused_3769_);
v___x_3762_ = v___x_3760_;
v_isShared_3763_ = v_isSharedCheck_3768_;
goto v_resetjp_3761_;
}
else
{
lean_dec(v___x_3760_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3768_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3764_ = lean_box(0);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 0, v___x_3764_);
v___x_3766_ = v___x_3762_;
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
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
v_a_3770_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3760_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3760_);
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
lean_dec(v_a_3472_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3453_);
lean_del_object(v___x_3450_);
lean_del_object(v___x_3441_);
lean_del_object(v___x_3434_);
lean_dec_ref(v_e_3405_);
return v___x_3685_;
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec(v_a_3472_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_del_object(v___x_3450_);
lean_del_object(v___x_3441_);
lean_dec(v_a_3439_);
lean_del_object(v___x_3434_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3780_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3473_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3473_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_del_object(v___x_3469_);
lean_dec(v_snd_3467_);
lean_dec(v_fst_3466_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_del_object(v___x_3450_);
lean_del_object(v___x_3441_);
lean_dec(v_a_3439_);
lean_del_object(v___x_3434_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3788_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3471_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3471_);
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
else
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
lean_dec(v_a_3458_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_del_object(v___x_3450_);
lean_del_object(v___x_3441_);
lean_dec(v_a_3439_);
lean_del_object(v___x_3434_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v___x_3798_ = lean_box(0);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3798_);
v___x_3800_ = v___x_3460_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_fst_3452_);
lean_del_object(v___x_3450_);
lean_del_object(v___x_3441_);
lean_dec(v_a_3439_);
lean_del_object(v___x_3434_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3803_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3457_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3457_);
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
}
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
lean_dec(v_a_3444_);
lean_del_object(v___x_3441_);
lean_dec(v_a_3439_);
lean_del_object(v___x_3434_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v___x_3813_ = lean_box(0);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3813_);
v___x_3815_ = v___x_3446_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_del_object(v___x_3441_);
lean_dec(v_a_3439_);
lean_del_object(v___x_3434_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3818_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3443_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3443_);
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
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_del_object(v___x_3434_);
lean_dec(v_a_3432_);
lean_dec_ref(v_e_3405_);
v_a_3827_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3436_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3436_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3836_, lean_object* v_expectedType_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3836_, v_expectedType_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3844_, lean_object* v_expectedType_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v___x_3851_; 
lean_inc_ref(v_expectedType_3845_);
lean_inc_ref(v_expr_3844_);
v___x_3851_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3844_, v_expectedType_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3931_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3854_ = v___x_3851_;
v_isShared_3855_ = v_isSharedCheck_3931_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3851_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3931_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
if (lean_obj_tag(v_a_3852_) == 1)
{
lean_object* v_val_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3868_; 
lean_dec_ref(v_expectedType_3845_);
lean_dec_ref(v_expr_3844_);
v_val_3856_ = lean_ctor_get(v_a_3852_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_a_3852_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3858_ = v_a_3852_;
v_isShared_3859_ = v_isSharedCheck_3868_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_val_3856_);
lean_dec(v_a_3852_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3868_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3860_ = lean_box(0);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v_val_3856_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v___x_3861_);
v___x_3863_ = v___x_3858_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3865_; 
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v___x_3863_);
v___x_3865_ = v___x_3854_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v___x_3869_; 
lean_del_object(v___x_3854_);
lean_dec(v_a_3852_);
lean_inc_ref(v_expectedType_3845_);
v___x_3869_ = l_Lean_Meta_whnfR(v_expectedType_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; uint8_t v___x_3871_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v___x_3871_ = l_Lean_Expr_isForall(v_a_3870_);
lean_dec(v_a_3870_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; 
v___x_3872_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3844_, v_expectedType_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
return v___x_3872_;
}
else
{
lean_object* v___x_3873_; 
lean_inc_ref(v_expr_3844_);
v___x_3873_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3844_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
if (lean_obj_tag(v_a_3874_) == 1)
{
lean_object* v_val_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3913_; 
v_val_3875_ = lean_ctor_get(v_a_3874_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_a_3874_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3877_ = v_a_3874_;
v_isShared_3878_ = v_isSharedCheck_3913_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_val_3875_);
lean_dec(v_a_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3913_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3879_; 
lean_inc(v_a_3849_);
lean_inc_ref(v_a_3848_);
lean_inc(v_a_3847_);
lean_inc_ref(v_a_3846_);
lean_inc(v_val_3875_);
v___x_3879_ = lean_infer_type(v_val_3875_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
lean_inc_ref(v_expectedType_3845_);
v___x_3881_ = l_Lean_Meta_isExprDefEq(v_a_3880_, v_expectedType_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3896_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3896_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3896_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
uint8_t v___x_3886_; 
v___x_3886_ = lean_unbox(v_a_3882_);
lean_dec(v_a_3882_);
if (v___x_3886_ == 0)
{
lean_object* v___x_3887_; 
lean_del_object(v___x_3884_);
lean_del_object(v___x_3877_);
lean_dec(v_val_3875_);
v___x_3887_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3844_, v_expectedType_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
return v___x_3887_;
}
else
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3891_; 
lean_dec_ref(v_expectedType_3845_);
lean_dec_ref(v_expr_3844_);
v___x_3888_ = lean_box(0);
v___x_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3889_, 0, v_val_3875_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v___x_3889_);
v___x_3891_ = v___x_3877_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3889_);
v___x_3891_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
lean_object* v___x_3893_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3891_);
v___x_3893_ = v___x_3884_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
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
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_del_object(v___x_3877_);
lean_dec(v_val_3875_);
lean_dec_ref(v_expectedType_3845_);
lean_dec_ref(v_expr_3844_);
v_a_3897_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3881_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3881_);
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
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_del_object(v___x_3877_);
lean_dec(v_val_3875_);
lean_dec_ref(v_expectedType_3845_);
lean_dec_ref(v_expr_3844_);
v_a_3905_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3879_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3879_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
}
else
{
lean_object* v___x_3914_; 
lean_dec(v_a_3874_);
v___x_3914_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3844_, v_expectedType_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
return v___x_3914_;
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v_expectedType_3845_);
lean_dec_ref(v_expr_3844_);
v_a_3915_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3873_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3873_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
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
lean_dec_ref(v_expectedType_3845_);
lean_dec_ref(v_expr_3844_);
v_a_3923_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3869_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3869_);
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
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v_expectedType_3845_);
lean_dec_ref(v_expr_3844_);
v_a_3932_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3851_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3851_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3940_, lean_object* v_expectedType_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3940_, v_expectedType_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3948_, lean_object* v_expectedType_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3948_, v_expectedType_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3980_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_3980_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3955_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3980_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
switch(lean_obj_tag(v_a_3956_))
{
case 0:
{
lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3960_ = lean_box(0);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3960_);
v___x_3962_ = v___x_3958_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
case 1:
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3975_; 
v_a_3964_ = lean_ctor_get(v_a_3956_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v_a_3956_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3966_ = v_a_3956_;
v_isShared_3967_ = v_isSharedCheck_3975_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v_a_3956_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3975_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v_fst_3968_; lean_object* v___x_3970_; 
v_fst_3968_ = lean_ctor_get(v_a_3964_, 0);
lean_inc(v_fst_3968_);
lean_dec(v_a_3964_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v_fst_3968_);
v___x_3970_ = v___x_3966_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_fst_3968_);
v___x_3970_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
lean_object* v___x_3972_; 
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3970_);
v___x_3972_ = v___x_3958_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3970_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
default: 
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3976_ = lean_box(2);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3976_);
v___x_3978_ = v___x_3958_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v_a_3981_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3955_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3955_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3989_, lean_object* v_expectedType_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_Meta_coerce_x3f(v_expr_3989_, v_expectedType_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
return v_res_3996_;
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
