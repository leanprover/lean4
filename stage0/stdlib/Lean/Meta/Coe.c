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
size_t v_x_36576__boxed_231_; uint8_t v_res_232_; lean_object* v_r_233_; 
v_x_36576__boxed_231_ = lean_unbox_usize(v_x_229_);
lean_dec(v_x_229_);
v_res_232_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_228_, v_x_36576__boxed_231_, v_x_230_);
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
v___x_353_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
lean_ctor_set(v___x_353_, 2, v___x_350_);
lean_ctor_set(v___x_353_, 3, v___x_351_);
lean_ctor_set(v___x_353_, 4, v___x_351_);
lean_ctor_set(v___x_353_, 5, v___x_351_);
lean_ctor_set(v___x_353_, 6, v___x_351_);
lean_ctor_set(v___x_353_, 7, v___x_349_);
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
v___y_392_ = v___y_446_;
v___y_393_ = v_ngen_452_;
v___y_394_ = v_infoState_457_;
v___y_395_ = v_nextMacroScope_451_;
v___y_396_ = v___y_444_;
v___y_397_ = v___y_445_;
v___y_398_ = v_recordedDeps_455_;
v___y_399_ = v_traceState_454_;
v___y_400_ = v_snapshotTasks_458_;
v___y_401_ = v_messages_456_;
v___y_402_ = v_auxDeclNGen_453_;
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
v___y_392_ = v___y_446_;
v___y_393_ = v_ngen_463_;
v___y_394_ = v_infoState_468_;
v___y_395_ = v_nextMacroScope_462_;
v___y_396_ = v___y_444_;
v___y_397_ = v___y_445_;
v___y_398_ = v_recordedDeps_466_;
v___y_399_ = v_traceState_465_;
v___y_400_ = v_snapshotTasks_469_;
v___y_401_ = v_messages_467_;
v___y_402_ = v_auxDeclNGen_464_;
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
lean_ctor_set(v___x_405_, 1, v___y_395_);
lean_ctor_set(v___x_405_, 2, v___y_393_);
lean_ctor_set(v___x_405_, 3, v___y_402_);
lean_ctor_set(v___x_405_, 4, v___y_399_);
lean_ctor_set(v___x_405_, 5, v___x_404_);
lean_ctor_set(v___x_405_, 6, v___y_398_);
lean_ctor_set(v___x_405_, 7, v___y_401_);
lean_ctor_set(v___x_405_, 8, v___y_394_);
lean_ctor_set(v___x_405_, 9, v___y_400_);
v___x_406_ = lean_st_ref_put(v___y_392_, v___x_405_);
v___x_407_ = lean_st_ref_take(v___y_397_);
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
v___x_419_ = lean_st_ref_put(v___y_397_, v___x_418_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_415_);
lean_ctor_set(v___x_420_, 1, v___y_396_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(lean_object* v___x_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed(lean_object* v___x_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(v___x_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object* v_a_1127_, lean_object* v_x_1128_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object* v_a_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_a_1136_, v_x_1137_);
lean_dec(v_x_1137_);
lean_dec_ref(v_a_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(lean_object* v_m_1139_, lean_object* v_a_1140_){
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
v___x_1156_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_a_1140_, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___boxed(lean_object* v_m_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_m_1157_, v_a_1158_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1180_, lean_object* v_pre_1181_, lean_object* v_post_1182_, lean_object* v_usedLetOnly_1183_, lean_object* v_skipConstInApp_1184_, lean_object* v_skipInstances_1185_, lean_object* v_body_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v_usedLetOnly_boxed_1195_; uint8_t v_skipConstInApp_boxed_1196_; uint8_t v_skipInstances_boxed_1197_; lean_object* v_res_1198_; 
v_usedLetOnly_boxed_1195_ = lean_unbox(v_usedLetOnly_1183_);
v_skipConstInApp_boxed_1196_ = lean_unbox(v_skipConstInApp_1184_);
v_skipInstances_boxed_1197_ = lean_unbox(v_skipInstances_1185_);
v_res_1198_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1180_, v_pre_1181_, v_post_1182_, v_usedLetOnly_boxed_1195_, v_skipConstInApp_boxed_1196_, v_skipInstances_boxed_1197_, v_body_1186_, v_x_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1188_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1202_, lean_object* v_pre_1203_, lean_object* v_post_1204_, uint8_t v_usedLetOnly_1205_, uint8_t v_skipConstInApp_1206_, uint8_t v_skipInstances_1207_, lean_object* v_body_1208_, lean_object* v_x_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_array_push(v_fvars_1202_, v_x_1209_);
v___x_1218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1203_, v_post_1204_, v_usedLetOnly_1205_, v_skipConstInApp_1206_, v_skipInstances_1207_, v___x_1217_, v_body_1208_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1219_, lean_object* v_pre_1220_, lean_object* v_post_1221_, lean_object* v_usedLetOnly_1222_, lean_object* v_skipConstInApp_1223_, lean_object* v_skipInstances_1224_, lean_object* v_body_1225_, lean_object* v_x_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
uint8_t v_usedLetOnly_boxed_1234_; uint8_t v_skipConstInApp_boxed_1235_; uint8_t v_skipInstances_boxed_1236_; lean_object* v_res_1237_; 
v_usedLetOnly_boxed_1234_ = lean_unbox(v_usedLetOnly_1222_);
v_skipConstInApp_boxed_1235_ = lean_unbox(v_skipConstInApp_1223_);
v_skipInstances_boxed_1236_ = lean_unbox(v_skipInstances_1224_);
v_res_1237_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1219_, v_pre_1220_, v_post_1221_, v_usedLetOnly_boxed_1234_, v_skipConstInApp_boxed_1235_, v_skipInstances_boxed_1236_, v_body_1225_, v_x_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1227_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_pre_1238_, lean_object* v_post_1239_, uint8_t v_usedLetOnly_1240_, uint8_t v_skipConstInApp_1241_, uint8_t v_skipInstances_1242_, lean_object* v_e_1243_, lean_object* v_a_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
lean_inc_ref(v_post_1239_);
lean_inc(v___y_1249_);
lean_inc_ref(v___y_1248_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc_ref(v_e_1243_);
v___x_1251_ = lean_apply_7(v_post_1239_, v_e_1243_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, lean_box(0));
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1283_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1283_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1283_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v_fst_1256_; lean_object* v_snd_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1282_; 
v_fst_1256_ = lean_ctor_get(v_a_1252_, 0);
v_snd_1257_ = lean_ctor_get(v_a_1252_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_a_1252_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1259_ = v_a_1252_;
v_isShared_1260_ = v_isSharedCheck_1282_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_snd_1257_);
lean_inc(v_fst_1256_);
lean_dec(v_a_1252_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1282_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___y_1262_; 
switch(lean_obj_tag(v_fst_1256_))
{
case 0:
{
lean_object* v_e_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1277_; 
lean_del_object(v___x_1259_);
lean_del_object(v___x_1254_);
lean_dec_ref(v_e_1243_);
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_pre_1238_);
v_e_1269_ = lean_ctor_get(v_fst_1256_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_fst_1256_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1271_ = v_fst_1256_;
v_isShared_1272_ = v_isSharedCheck_1277_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_e_1269_);
lean_dec(v_fst_1256_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1277_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_e_1269_);
lean_ctor_set(v___x_1273_, 1, v_snd_1257_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1273_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
case 1:
{
lean_object* v_e_1278_; lean_object* v___x_1279_; 
lean_del_object(v___x_1259_);
lean_del_object(v___x_1254_);
lean_dec_ref(v_e_1243_);
v_e_1278_ = lean_ctor_get(v_fst_1256_, 0);
lean_inc_ref(v_e_1278_);
lean_dec_ref_known(v_fst_1256_, 1);
v___x_1279_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1238_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v_e_1278_, v_a_1244_, v_snd_1257_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
return v___x_1279_;
}
default: 
{
lean_object* v_e_x3f_1280_; 
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_pre_1238_);
v_e_x3f_1280_ = lean_ctor_get(v_fst_1256_, 0);
lean_inc(v_e_x3f_1280_);
lean_dec_ref_known(v_fst_1256_, 1);
if (lean_obj_tag(v_e_x3f_1280_) == 0)
{
v___y_1262_ = v_e_1243_;
goto v___jp_1261_;
}
else
{
lean_object* v_val_1281_; 
lean_dec_ref(v_e_1243_);
v_val_1281_ = lean_ctor_get(v_e_x3f_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v_e_x3f_1280_, 1);
v___y_1262_ = v_val_1281_;
goto v___jp_1261_;
}
}
}
v___jp_1261_:
{
lean_object* v___x_1264_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___y_1262_);
v___x_1264_ = v___x_1259_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___y_1262_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_snd_1257_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1266_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1264_);
v___x_1266_ = v___x_1254_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_e_1243_);
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_pre_1238_);
v_a_1284_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1251_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1251_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1292_, lean_object* v_post_1293_, uint8_t v_usedLetOnly_1294_, uint8_t v_skipConstInApp_1295_, uint8_t v_skipInstances_1296_, lean_object* v_fvars_1297_, lean_object* v_e_1298_, lean_object* v_a_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
if (lean_obj_tag(v_e_1298_) == 6)
{
lean_object* v_binderName_1306_; lean_object* v_binderType_1307_; lean_object* v_body_1308_; uint8_t v_binderInfo_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___f_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_binderName_1306_ = lean_ctor_get(v_e_1298_, 0);
lean_inc(v_binderName_1306_);
v_binderType_1307_ = lean_ctor_get(v_e_1298_, 1);
lean_inc_ref(v_binderType_1307_);
v_body_1308_ = lean_ctor_get(v_e_1298_, 2);
lean_inc_ref(v_body_1308_);
v_binderInfo_1309_ = lean_ctor_get_uint8(v_e_1298_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1298_, 3);
v___x_1310_ = lean_box(v_usedLetOnly_1294_);
v___x_1311_ = lean_box(v_skipConstInApp_1295_);
v___x_1312_ = lean_box(v_skipInstances_1296_);
lean_inc_ref(v_post_1293_);
lean_inc_ref(v_pre_1292_);
lean_inc_ref(v_fvars_1297_);
v___f_1313_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1313_, 0, v_fvars_1297_);
lean_closure_set(v___f_1313_, 1, v_pre_1292_);
lean_closure_set(v___f_1313_, 2, v_post_1293_);
lean_closure_set(v___f_1313_, 3, v___x_1310_);
lean_closure_set(v___f_1313_, 4, v___x_1311_);
lean_closure_set(v___f_1313_, 5, v___x_1312_);
lean_closure_set(v___f_1313_, 6, v_body_1308_);
v___x_1314_ = lean_expr_instantiate_rev(v_binderType_1307_, v_fvars_1297_);
lean_dec_ref(v_fvars_1297_);
lean_dec_ref(v_binderType_1307_);
v___x_1315_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1292_, v_post_1293_, v_usedLetOnly_1294_, v_skipConstInApp_1295_, v_skipInstances_1296_, v___x_1314_, v_a_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v_fst_1317_; lean_object* v_snd_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v_fst_1317_ = lean_ctor_get(v_a_1316_, 0);
lean_inc(v_fst_1317_);
v_snd_1318_ = lean_ctor_get(v_a_1316_, 1);
lean_inc(v_snd_1318_);
lean_dec(v_a_1316_);
v___x_1319_ = 0;
v___x_1320_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_binderName_1306_, v_binderInfo_1309_, v_fst_1317_, v___f_1313_, v___x_1319_, v_a_1299_, v_snd_1318_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1320_;
}
else
{
lean_dec_ref(v___f_1313_);
lean_dec(v_binderName_1306_);
return v___x_1315_;
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_expr_instantiate_rev(v_e_1298_, v_fvars_1297_);
lean_dec_ref(v_e_1298_);
lean_inc_ref(v_post_1293_);
lean_inc_ref(v_pre_1292_);
v___x_1322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1292_, v_post_1293_, v_usedLetOnly_1294_, v_skipConstInApp_1295_, v_skipInstances_1296_, v___x_1321_, v_a_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v_fst_1324_; lean_object* v_snd_1325_; uint8_t v___x_1326_; uint8_t v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v_fst_1324_ = lean_ctor_get(v_a_1323_, 0);
lean_inc(v_fst_1324_);
v_snd_1325_ = lean_ctor_get(v_a_1323_, 1);
lean_inc(v_snd_1325_);
lean_dec(v_a_1323_);
v___x_1326_ = 0;
v___x_1327_ = 1;
v___x_1328_ = 1;
v___x_1329_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1297_, v_fst_1324_, v___x_1326_, v_usedLetOnly_1294_, v___x_1326_, v___x_1327_, v___x_1328_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec_ref(v_fvars_1297_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1331_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v___x_1331_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1292_, v_post_1293_, v_usedLetOnly_1294_, v_skipConstInApp_1295_, v_skipInstances_1296_, v_a_1330_, v_a_1299_, v_snd_1325_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1331_;
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec(v_snd_1325_);
lean_dec_ref(v_post_1293_);
lean_dec_ref(v_pre_1292_);
v_a_1332_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1329_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1329_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1297_);
lean_dec_ref(v_post_1293_);
lean_dec_ref(v_pre_1292_);
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(lean_object* v_fvars_1340_, lean_object* v_pre_1341_, lean_object* v_post_1342_, uint8_t v_usedLetOnly_1343_, uint8_t v_skipConstInApp_1344_, uint8_t v_skipInstances_1345_, lean_object* v_body_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_array_push(v_fvars_1340_, v_x_1347_);
v___x_1356_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1341_, v_post_1342_, v_usedLetOnly_1343_, v_skipConstInApp_1344_, v_skipInstances_1345_, v___x_1355_, v_body_1346_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed(lean_object* v_fvars_1357_, lean_object* v_pre_1358_, lean_object* v_post_1359_, lean_object* v_usedLetOnly_1360_, lean_object* v_skipConstInApp_1361_, lean_object* v_skipInstances_1362_, lean_object* v_body_1363_, lean_object* v_x_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
uint8_t v_usedLetOnly_boxed_1372_; uint8_t v_skipConstInApp_boxed_1373_; uint8_t v_skipInstances_boxed_1374_; lean_object* v_res_1375_; 
v_usedLetOnly_boxed_1372_ = lean_unbox(v_usedLetOnly_1360_);
v_skipConstInApp_boxed_1373_ = lean_unbox(v_skipConstInApp_1361_);
v_skipInstances_boxed_1374_ = lean_unbox(v_skipInstances_1362_);
v_res_1375_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(v_fvars_1357_, v_pre_1358_, v_post_1359_, v_usedLetOnly_boxed_1372_, v_skipConstInApp_boxed_1373_, v_skipInstances_boxed_1374_, v_body_1363_, v_x_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1365_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(lean_object* v_pre_1376_, lean_object* v_post_1377_, uint8_t v_usedLetOnly_1378_, uint8_t v_skipConstInApp_1379_, uint8_t v_skipInstances_1380_, lean_object* v_fvars_1381_, lean_object* v_e_1382_, lean_object* v_a_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
if (lean_obj_tag(v_e_1382_) == 8)
{
lean_object* v_declName_1390_; lean_object* v_type_1391_; lean_object* v_value_1392_; lean_object* v_body_1393_; uint8_t v_nondep_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___f_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v_declName_1390_ = lean_ctor_get(v_e_1382_, 0);
lean_inc(v_declName_1390_);
v_type_1391_ = lean_ctor_get(v_e_1382_, 1);
lean_inc_ref(v_type_1391_);
v_value_1392_ = lean_ctor_get(v_e_1382_, 2);
lean_inc_ref(v_value_1392_);
v_body_1393_ = lean_ctor_get(v_e_1382_, 3);
lean_inc_ref(v_body_1393_);
v_nondep_1394_ = lean_ctor_get_uint8(v_e_1382_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1382_, 4);
v___x_1395_ = lean_box(v_usedLetOnly_1378_);
v___x_1396_ = lean_box(v_skipConstInApp_1379_);
v___x_1397_ = lean_box(v_skipInstances_1380_);
lean_inc_ref_n(v_post_1377_, 2);
lean_inc_ref_n(v_pre_1376_, 2);
lean_inc_ref(v_fvars_1381_);
v___f_1398_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1398_, 0, v_fvars_1381_);
lean_closure_set(v___f_1398_, 1, v_pre_1376_);
lean_closure_set(v___f_1398_, 2, v_post_1377_);
lean_closure_set(v___f_1398_, 3, v___x_1395_);
lean_closure_set(v___f_1398_, 4, v___x_1396_);
lean_closure_set(v___f_1398_, 5, v___x_1397_);
lean_closure_set(v___f_1398_, 6, v_body_1393_);
v___x_1399_ = lean_expr_instantiate_rev(v_type_1391_, v_fvars_1381_);
lean_dec_ref(v_type_1391_);
v___x_1400_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1376_, v_post_1377_, v_usedLetOnly_1378_, v_skipConstInApp_1379_, v_skipInstances_1380_, v___x_1399_, v_a_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v_fst_1402_; lean_object* v_snd_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v_fst_1402_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_fst_1402_);
v_snd_1403_ = lean_ctor_get(v_a_1401_, 1);
lean_inc(v_snd_1403_);
lean_dec(v_a_1401_);
v___x_1404_ = lean_expr_instantiate_rev(v_value_1392_, v_fvars_1381_);
lean_dec_ref(v_fvars_1381_);
lean_dec_ref(v_value_1392_);
v___x_1405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1376_, v_post_1377_, v_usedLetOnly_1378_, v_skipConstInApp_1379_, v_skipInstances_1380_, v___x_1404_, v_a_1383_, v_snd_1403_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_fst_1407_; lean_object* v_snd_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v_fst_1407_ = lean_ctor_get(v_a_1406_, 0);
lean_inc(v_fst_1407_);
v_snd_1408_ = lean_ctor_get(v_a_1406_, 1);
lean_inc(v_snd_1408_);
lean_dec(v_a_1406_);
v___x_1409_ = 0;
v___x_1410_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(v_declName_1390_, v_fst_1402_, v_fst_1407_, v___f_1398_, v_nondep_1394_, v___x_1409_, v_a_1383_, v_snd_1408_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
return v___x_1410_;
}
else
{
lean_dec(v_fst_1402_);
lean_dec_ref(v___f_1398_);
lean_dec(v_declName_1390_);
return v___x_1405_;
}
}
else
{
lean_dec_ref(v___f_1398_);
lean_dec_ref(v_value_1392_);
lean_dec(v_declName_1390_);
lean_dec_ref(v_fvars_1381_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1376_);
return v___x_1400_;
}
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_expr_instantiate_rev(v_e_1382_, v_fvars_1381_);
lean_dec_ref(v_e_1382_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1376_);
v___x_1412_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1376_, v_post_1377_, v_usedLetOnly_1378_, v_skipConstInApp_1379_, v_skipInstances_1380_, v___x_1411_, v_a_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v_fst_1414_; lean_object* v_snd_1415_; uint8_t v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v_fst_1414_ = lean_ctor_get(v_a_1413_, 0);
lean_inc(v_fst_1414_);
v_snd_1415_ = lean_ctor_get(v_a_1413_, 1);
lean_inc(v_snd_1415_);
lean_dec(v_a_1413_);
v___x_1416_ = 0;
v___x_1417_ = 1;
v___x_1418_ = l_Lean_Meta_mkLetFVars(v_fvars_1381_, v_fst_1414_, v_usedLetOnly_1378_, v___x_1416_, v___x_1417_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec_ref(v_fvars_1381_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1376_, v_post_1377_, v_usedLetOnly_1378_, v_skipConstInApp_1379_, v_skipInstances_1380_, v_a_1419_, v_a_1383_, v_snd_1415_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
return v___x_1420_;
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_snd_1415_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1376_);
v_a_1421_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1418_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1418_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1381_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1376_);
return v___x_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1429_, lean_object* v_post_1430_, uint8_t v_usedLetOnly_1431_, uint8_t v_skipConstInApp_1432_, uint8_t v_skipInstances_1433_, size_t v_sz_1434_, size_t v_i_1435_, lean_object* v_bs_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_usize_dec_lt(v_i_1435_, v_sz_1434_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v_post_1430_);
lean_dec_ref(v_pre_1429_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_bs_1436_);
lean_ctor_set(v___x_1445_, 1, v___y_1438_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
else
{
lean_object* v_v_1447_; lean_object* v___x_1448_; lean_object* v_bs_x27_1449_; lean_object* v___x_1450_; 
v_v_1447_ = lean_array_uget(v_bs_1436_, v_i_1435_);
v___x_1448_ = lean_unsigned_to_nat(0u);
v_bs_x27_1449_ = lean_array_uset(v_bs_1436_, v_i_1435_, v___x_1448_);
lean_inc_ref(v_post_1430_);
lean_inc_ref(v_pre_1429_);
v___x_1450_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1429_, v_post_1430_, v_usedLetOnly_1431_, v_skipConstInApp_1432_, v_skipInstances_1433_, v_v_1447_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v_fst_1452_; lean_object* v_snd_1453_; size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v_fst_1452_ = lean_ctor_get(v_a_1451_, 0);
lean_inc(v_fst_1452_);
v_snd_1453_ = lean_ctor_get(v_a_1451_, 1);
lean_inc(v_snd_1453_);
lean_dec(v_a_1451_);
v___x_1454_ = ((size_t)1ULL);
v___x_1455_ = lean_usize_add(v_i_1435_, v___x_1454_);
v___x_1456_ = lean_array_uset(v_bs_x27_1449_, v_i_1435_, v_fst_1452_);
v_i_1435_ = v___x_1455_;
v_bs_1436_ = v___x_1456_;
v___y_1438_ = v_snd_1453_;
goto _start;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_bs_x27_1449_);
lean_dec_ref(v_post_1430_);
lean_dec_ref(v_pre_1429_);
v_a_1458_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1450_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1450_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(lean_object* v_pre_1466_, lean_object* v_post_1467_, uint8_t v_usedLetOnly_1468_, uint8_t v_skipConstInApp_1469_, uint8_t v_skipInstances_1470_, lean_object* v___x_1471_, lean_object* v___y_1472_, lean_object* v_b_1473_, lean_object* v_a_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1466_, v_post_1467_, v_usedLetOnly_1468_, v_skipConstInApp_1469_, v_skipInstances_1470_, v___x_1471_, v___y_1472_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1500_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1500_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1500_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_fst_1486_; lean_object* v_snd_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1499_; 
v_fst_1486_ = lean_ctor_get(v_a_1482_, 0);
v_snd_1487_ = lean_ctor_get(v_a_1482_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_a_1482_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1489_ = v_a_1482_;
v_isShared_1490_ = v_isSharedCheck_1499_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snd_1487_);
lean_inc(v_fst_1486_);
lean_dec(v_a_1482_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1499_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1491_ = lean_array_fset(v_b_1473_, v_a_1474_, v_fst_1486_);
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1492_);
v___x_1494_ = v___x_1489_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_snd_1487_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1494_);
v___x_1496_ = v___x_1484_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec_ref(v_b_1473_);
v_a_1501_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1481_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1481_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed(lean_object* v_pre_1509_, lean_object* v_post_1510_, lean_object* v_usedLetOnly_1511_, lean_object* v_skipConstInApp_1512_, lean_object* v_skipInstances_1513_, lean_object* v___x_1514_, lean_object* v___y_1515_, lean_object* v_b_1516_, lean_object* v_a_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
uint8_t v_usedLetOnly_boxed_1524_; uint8_t v_skipConstInApp_boxed_1525_; uint8_t v_skipInstances_boxed_1526_; lean_object* v_res_1527_; 
v_usedLetOnly_boxed_1524_ = lean_unbox(v_usedLetOnly_1511_);
v_skipConstInApp_boxed_1525_ = lean_unbox(v_skipConstInApp_1512_);
v_skipInstances_boxed_1526_ = lean_unbox(v_skipInstances_1513_);
v_res_1527_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(v_pre_1509_, v_post_1510_, v_usedLetOnly_boxed_1524_, v_skipConstInApp_boxed_1525_, v_skipInstances_boxed_1526_, v___x_1514_, v___y_1515_, v_b_1516_, v_a_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v_a_1517_);
lean_dec(v___y_1515_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_1528_, lean_object* v___x_1529_, lean_object* v_pre_1530_, lean_object* v_post_1531_, uint8_t v_usedLetOnly_1532_, uint8_t v_skipConstInApp_1533_, uint8_t v_skipInstances_1534_, lean_object* v_a_1535_, lean_object* v_b_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___y_1545_; uint8_t v___x_1579_; 
v___x_1579_ = lean_nat_dec_lt(v_a_1535_, v_upperBound_1528_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec(v_a_1535_);
lean_dec_ref(v_post_1531_);
lean_dec_ref(v_pre_1530_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_b_1536_);
lean_ctor_set(v___x_1580_, 1, v___y_1538_);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1582_ = lean_array_fget_borrowed(v_b_1536_, v_a_1535_);
v___x_1583_ = lean_array_get_size(v___x_1529_);
v___x_1584_ = lean_nat_dec_lt(v_a_1535_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___f_1588_; 
lean_inc(v___x_1582_);
v___x_1585_ = lean_box(v_usedLetOnly_1532_);
v___x_1586_ = lean_box(v_skipConstInApp_1533_);
v___x_1587_ = lean_box(v_skipInstances_1534_);
lean_inc(v_a_1535_);
lean_inc(v___y_1537_);
lean_inc_ref(v_post_1531_);
lean_inc_ref(v_pre_1530_);
v___f_1588_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1588_, 0, v_pre_1530_);
lean_closure_set(v___f_1588_, 1, v_post_1531_);
lean_closure_set(v___f_1588_, 2, v___x_1585_);
lean_closure_set(v___f_1588_, 3, v___x_1586_);
lean_closure_set(v___f_1588_, 4, v___x_1587_);
lean_closure_set(v___f_1588_, 5, v___x_1582_);
lean_closure_set(v___f_1588_, 6, v___y_1537_);
lean_closure_set(v___f_1588_, 7, v_b_1536_);
lean_closure_set(v___f_1588_, 8, v_a_1535_);
v___y_1545_ = v___f_1588_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1589_; uint8_t v_isInstance_1590_; 
v___x_1589_ = lean_array_fget_borrowed(v___x_1529_, v_a_1535_);
v_isInstance_1590_ = lean_ctor_get_uint8(v___x_1589_, sizeof(void*)*1 + 4);
if (v_isInstance_1590_ == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___f_1594_; 
lean_inc(v___x_1582_);
v___x_1591_ = lean_box(v_usedLetOnly_1532_);
v___x_1592_ = lean_box(v_skipConstInApp_1533_);
v___x_1593_ = lean_box(v_skipInstances_1534_);
lean_inc(v_a_1535_);
lean_inc(v___y_1537_);
lean_inc_ref(v_post_1531_);
lean_inc_ref(v_pre_1530_);
v___f_1594_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1594_, 0, v_pre_1530_);
lean_closure_set(v___f_1594_, 1, v_post_1531_);
lean_closure_set(v___f_1594_, 2, v___x_1591_);
lean_closure_set(v___f_1594_, 3, v___x_1592_);
lean_closure_set(v___f_1594_, 4, v___x_1593_);
lean_closure_set(v___f_1594_, 5, v___x_1582_);
lean_closure_set(v___f_1594_, 6, v___y_1537_);
lean_closure_set(v___f_1594_, 7, v_b_1536_);
lean_closure_set(v___f_1594_, 8, v_a_1535_);
v___y_1545_ = v___f_1594_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1595_; lean_object* v___f_1596_; 
v___x_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1595_, 0, v_b_1536_);
v___f_1596_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1596_, 0, v___x_1595_);
v___y_1545_ = v___f_1596_;
goto v___jp_1544_;
}
}
}
v___jp_1544_:
{
lean_object* v___x_1546_; 
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
v___x_1546_ = lean_apply_6(v___y_1545_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1570_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1570_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1570_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_fst_1551_; 
v_fst_1551_ = lean_ctor_get(v_a_1547_, 0);
lean_inc(v_fst_1551_);
if (lean_obj_tag(v_fst_1551_) == 0)
{
lean_object* v_snd_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_a_1535_);
lean_dec_ref(v_post_1531_);
lean_dec_ref(v_pre_1530_);
v_snd_1552_ = lean_ctor_get(v_a_1547_, 1);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_a_1547_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; 
v_unused_1564_ = lean_ctor_get(v_a_1547_, 0);
lean_dec(v_unused_1564_);
v___x_1554_ = v_a_1547_;
v_isShared_1555_ = v_isSharedCheck_1563_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_snd_1552_);
lean_dec(v_a_1547_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1563_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_a_1556_; lean_object* v___x_1558_; 
v_a_1556_ = lean_ctor_get(v_fst_1551_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v_fst_1551_, 1);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v_a_1556_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_snd_1552_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1558_);
v___x_1560_ = v___x_1549_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_snd_1565_; lean_object* v_a_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_del_object(v___x_1549_);
v_snd_1565_ = lean_ctor_get(v_a_1547_, 1);
lean_inc(v_snd_1565_);
lean_dec(v_a_1547_);
v_a_1566_ = lean_ctor_get(v_fst_1551_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v_fst_1551_, 1);
v___x_1567_ = lean_unsigned_to_nat(1u);
v___x_1568_ = lean_nat_add(v_a_1535_, v___x_1567_);
lean_dec(v_a_1535_);
v_a_1535_ = v___x_1568_;
v_b_1536_ = v_a_1566_;
v___y_1538_ = v_snd_1565_;
goto _start;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_a_1535_);
lean_dec_ref(v_post_1531_);
lean_dec_ref(v_pre_1530_);
v_a_1571_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1546_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1546_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(uint8_t v_skipInstances_1597_, lean_object* v_pre_1598_, lean_object* v_post_1599_, uint8_t v_usedLetOnly_1600_, uint8_t v_skipConstInApp_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_f_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; 
if (lean_obj_tag(v_x_1602_) == 5)
{
lean_object* v_fn_1668_; lean_object* v_arg_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_fn_1668_ = lean_ctor_get(v_x_1602_, 0);
lean_inc_ref(v_fn_1668_);
v_arg_1669_ = lean_ctor_get(v_x_1602_, 1);
lean_inc_ref(v_arg_1669_);
lean_dec_ref_known(v_x_1602_, 2);
v___x_1670_ = lean_array_set(v_x_1603_, v_x_1604_, v_arg_1669_);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_sub(v_x_1604_, v___x_1671_);
lean_dec(v_x_1604_);
v_x_1602_ = v_fn_1668_;
v_x_1603_ = v___x_1670_;
v_x_1604_ = v___x_1672_;
goto _start;
}
else
{
lean_dec(v_x_1604_);
if (v_skipConstInApp_1601_ == 0)
{
goto v___jp_1663_;
}
else
{
uint8_t v___x_1674_; 
v___x_1674_ = l_Lean_Expr_isConst(v_x_1602_);
if (v___x_1674_ == 0)
{
goto v___jp_1663_;
}
else
{
v_f_1613_ = v_x_1602_;
v___y_1614_ = v___y_1605_;
v___y_1615_ = v___y_1606_;
v___y_1616_ = v___y_1607_;
v___y_1617_ = v___y_1608_;
v___y_1618_ = v___y_1609_;
v___y_1619_ = v___y_1610_;
goto v___jp_1612_;
}
}
}
v___jp_1612_:
{
if (v_skipInstances_1597_ == 0)
{
size_t v_sz_1620_; size_t v___x_1621_; lean_object* v___x_1622_; 
v_sz_1620_ = lean_array_size(v_x_1603_);
v___x_1621_ = ((size_t)0ULL);
lean_inc_ref(v_post_1599_);
lean_inc_ref(v_pre_1598_);
v___x_1622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1598_, v_post_1599_, v_usedLetOnly_1600_, v_skipConstInApp_1601_, v_skipInstances_1597_, v_sz_1620_, v___x_1621_, v_x_1603_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v_fst_1624_; lean_object* v_snd_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v_fst_1624_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_fst_1624_);
v_snd_1625_ = lean_ctor_get(v_a_1623_, 1);
lean_inc(v_snd_1625_);
lean_dec(v_a_1623_);
v___x_1626_ = l_Lean_mkAppN(v_f_1613_, v_fst_1624_);
lean_dec(v_fst_1624_);
v___x_1627_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1598_, v_post_1599_, v_usedLetOnly_1600_, v_skipConstInApp_1601_, v_skipInstances_1597_, v___x_1626_, v___y_1614_, v_snd_1625_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1627_;
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref(v_f_1613_);
lean_dec_ref(v_post_1599_);
lean_dec_ref(v_pre_1598_);
v_a_1628_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1622_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1622_);
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
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_array_get_size(v_x_1603_);
lean_inc_ref(v_f_1613_);
v___x_1637_ = l_Lean_Meta_getFunInfoNArgs(v_f_1613_, v___x_1636_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v_paramInfo_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v_paramInfo_1639_ = lean_ctor_get(v_a_1638_, 0);
lean_inc_ref(v_paramInfo_1639_);
lean_dec(v_a_1638_);
v___x_1640_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1599_);
lean_inc_ref(v_pre_1598_);
v___x_1641_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v___x_1636_, v_paramInfo_1639_, v_pre_1598_, v_post_1599_, v_usedLetOnly_1600_, v_skipConstInApp_1601_, v_skipInstances_1597_, v___x_1640_, v_x_1603_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec_ref(v_paramInfo_1639_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v_fst_1643_; lean_object* v_snd_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v_fst_1643_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_fst_1643_);
v_snd_1644_ = lean_ctor_get(v_a_1642_, 1);
lean_inc(v_snd_1644_);
lean_dec(v_a_1642_);
v___x_1645_ = l_Lean_mkAppN(v_f_1613_, v_fst_1643_);
lean_dec(v_fst_1643_);
v___x_1646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1598_, v_post_1599_, v_usedLetOnly_1600_, v_skipConstInApp_1601_, v_skipInstances_1597_, v___x_1645_, v___y_1614_, v_snd_1644_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1646_;
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref(v_f_1613_);
lean_dec_ref(v_post_1599_);
lean_dec_ref(v_pre_1598_);
v_a_1647_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1641_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1641_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec(v___y_1615_);
lean_dec_ref(v_f_1613_);
lean_dec_ref(v_x_1603_);
lean_dec_ref(v_post_1599_);
lean_dec_ref(v_pre_1598_);
v_a_1655_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1637_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1637_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
v___jp_1663_:
{
lean_object* v___x_1664_; 
lean_inc_ref(v_post_1599_);
lean_inc_ref(v_pre_1598_);
v___x_1664_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1598_, v_post_1599_, v_usedLetOnly_1600_, v_skipConstInApp_1601_, v_skipInstances_1597_, v_x_1602_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v_fst_1666_; lean_object* v_snd_1667_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v_fst_1666_ = lean_ctor_get(v_a_1665_, 0);
lean_inc(v_fst_1666_);
v_snd_1667_ = lean_ctor_get(v_a_1665_, 1);
lean_inc(v_snd_1667_);
lean_dec(v_a_1665_);
v_f_1613_ = v_fst_1666_;
v___y_1614_ = v___y_1605_;
v___y_1615_ = v_snd_1667_;
v___y_1616_ = v___y_1607_;
v___y_1617_ = v___y_1608_;
v___y_1618_ = v___y_1609_;
v___y_1619_ = v___y_1610_;
goto v___jp_1612_;
}
else
{
lean_dec_ref(v_x_1603_);
lean_dec_ref(v_post_1599_);
lean_dec_ref(v_pre_1598_);
return v___x_1664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1675_, lean_object* v_pre_1676_, lean_object* v_e_1677_, lean_object* v_post_1678_, uint8_t v_usedLetOnly_1679_, uint8_t v_skipConstInApp_1680_, uint8_t v_skipInstances_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_Core_checkSystem(v___x_1675_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref_known(v___x_1689_, 1);
lean_inc_ref(v_pre_1676_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
lean_inc_ref(v_e_1677_);
v___x_1690_ = lean_apply_7(v_pre_1676_, v_e_1677_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, lean_box(0));
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1752_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1752_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1752_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_fst_1695_; lean_object* v_snd_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1751_; 
v_fst_1695_ = lean_ctor_get(v_a_1691_, 0);
v_snd_1696_ = lean_ctor_get(v_a_1691_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_a_1691_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1698_ = v_a_1691_;
v_isShared_1699_ = v_isSharedCheck_1751_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_snd_1696_);
lean_inc(v_fst_1695_);
lean_dec(v_a_1691_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1751_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___y_1701_; 
switch(lean_obj_tag(v_fst_1695_))
{
case 0:
{
lean_object* v_e_1740_; lean_object* v___x_1742_; 
lean_dec_ref(v_post_1678_);
lean_dec_ref(v_e_1677_);
lean_dec_ref(v_pre_1676_);
v_e_1740_ = lean_ctor_get(v_fst_1695_, 0);
lean_inc_ref(v_e_1740_);
lean_dec_ref_known(v_fst_1695_, 1);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v_e_1740_);
v___x_1742_ = v___x_1698_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_e_1740_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_snd_1696_);
v___x_1742_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1744_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1742_);
v___x_1744_ = v___x_1693_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
case 1:
{
lean_object* v_e_1747_; lean_object* v___x_1748_; 
lean_del_object(v___x_1698_);
lean_del_object(v___x_1693_);
lean_dec_ref(v_e_1677_);
v_e_1747_ = lean_ctor_get(v_fst_1695_, 0);
lean_inc_ref(v_e_1747_);
lean_dec_ref_known(v_fst_1695_, 1);
v___x_1748_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v_e_1747_, v___y_1682_, v_snd_1696_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1748_;
}
default: 
{
lean_object* v_e_x3f_1749_; 
lean_del_object(v___x_1698_);
lean_del_object(v___x_1693_);
v_e_x3f_1749_ = lean_ctor_get(v_fst_1695_, 0);
lean_inc(v_e_x3f_1749_);
lean_dec_ref_known(v_fst_1695_, 1);
if (lean_obj_tag(v_e_x3f_1749_) == 0)
{
v___y_1701_ = v_e_1677_;
goto v___jp_1700_;
}
else
{
lean_object* v_val_1750_; 
lean_dec_ref(v_e_1677_);
v_val_1750_ = lean_ctor_get(v_e_x3f_1749_, 0);
lean_inc(v_val_1750_);
lean_dec_ref_known(v_e_x3f_1749_, 1);
v___y_1701_ = v_val_1750_;
goto v___jp_1700_;
}
}
}
v___jp_1700_:
{
switch(lean_obj_tag(v___y_1701_))
{
case 7:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1703_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v___x_1702_, v___y_1701_, v___y_1682_, v_snd_1696_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1703_;
}
case 6:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1705_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v___x_1704_, v___y_1701_, v___y_1682_, v_snd_1696_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1705_;
}
case 8:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1707_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v___x_1706_, v___y_1701_, v___y_1682_, v_snd_1696_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1707_;
}
case 5:
{
lean_object* v_dummy_1708_; lean_object* v_nargs_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_dummy_1708_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1709_ = l_Lean_Expr_getAppNumArgs(v___y_1701_);
lean_inc(v_nargs_1709_);
v___x_1710_ = lean_mk_array(v_nargs_1709_, v_dummy_1708_);
v___x_1711_ = lean_unsigned_to_nat(1u);
v___x_1712_ = lean_nat_sub(v_nargs_1709_, v___x_1711_);
lean_dec(v_nargs_1709_);
v___x_1713_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_skipInstances_1681_, v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v___y_1701_, v___x_1710_, v___x_1712_, v___y_1682_, v_snd_1696_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1713_;
}
case 10:
{
lean_object* v_data_1714_; lean_object* v_expr_1715_; lean_object* v___x_1716_; 
v_data_1714_ = lean_ctor_get(v___y_1701_, 0);
v_expr_1715_ = lean_ctor_get(v___y_1701_, 1);
lean_inc_ref(v_expr_1715_);
lean_inc_ref(v_post_1678_);
lean_inc_ref(v_pre_1676_);
v___x_1716_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v_expr_1715_, v___y_1682_, v_snd_1696_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v_fst_1718_; lean_object* v_snd_1719_; size_t v___x_1720_; size_t v___x_1721_; uint8_t v___x_1722_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v_fst_1718_ = lean_ctor_get(v_a_1717_, 0);
lean_inc(v_fst_1718_);
v_snd_1719_ = lean_ctor_get(v_a_1717_, 1);
lean_inc(v_snd_1719_);
lean_dec(v_a_1717_);
v___x_1720_ = lean_ptr_addr(v_expr_1715_);
v___x_1721_ = lean_ptr_addr(v_fst_1718_);
v___x_1722_ = lean_usize_dec_eq(v___x_1720_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_inc(v_data_1714_);
lean_dec_ref_known(v___y_1701_, 2);
v___x_1723_ = l_Lean_Expr_mdata___override(v_data_1714_, v_fst_1718_);
v___x_1724_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v___x_1723_, v___y_1682_, v_snd_1719_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; 
lean_dec(v_fst_1718_);
v___x_1725_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v___y_1701_, v___y_1682_, v_snd_1719_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1725_;
}
}
else
{
lean_dec_ref_known(v___y_1701_, 2);
lean_dec_ref(v_post_1678_);
lean_dec_ref(v_pre_1676_);
return v___x_1716_;
}
}
case 11:
{
lean_object* v_typeName_1726_; lean_object* v_idx_1727_; lean_object* v_struct_1728_; lean_object* v___x_1729_; 
v_typeName_1726_ = lean_ctor_get(v___y_1701_, 0);
v_idx_1727_ = lean_ctor_get(v___y_1701_, 1);
v_struct_1728_ = lean_ctor_get(v___y_1701_, 2);
lean_inc_ref(v_struct_1728_);
lean_inc_ref(v_post_1678_);
lean_inc_ref(v_pre_1676_);
v___x_1729_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v_struct_1728_, v___y_1682_, v_snd_1696_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v_fst_1731_; lean_object* v_snd_1732_; size_t v___x_1733_; size_t v___x_1734_; uint8_t v___x_1735_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v_fst_1731_ = lean_ctor_get(v_a_1730_, 0);
lean_inc(v_fst_1731_);
v_snd_1732_ = lean_ctor_get(v_a_1730_, 1);
lean_inc(v_snd_1732_);
lean_dec(v_a_1730_);
v___x_1733_ = lean_ptr_addr(v_struct_1728_);
v___x_1734_ = lean_ptr_addr(v_fst_1731_);
v___x_1735_ = lean_usize_dec_eq(v___x_1733_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_inc(v_idx_1727_);
lean_inc(v_typeName_1726_);
lean_dec_ref_known(v___y_1701_, 3);
v___x_1736_ = l_Lean_Expr_proj___override(v_typeName_1726_, v_idx_1727_, v_fst_1731_);
v___x_1737_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v___x_1736_, v___y_1682_, v_snd_1732_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; 
lean_dec(v_fst_1731_);
v___x_1738_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v___y_1701_, v___y_1682_, v_snd_1732_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1738_;
}
}
else
{
lean_dec_ref_known(v___y_1701_, 3);
lean_dec_ref(v_post_1678_);
lean_dec_ref(v_pre_1676_);
return v___x_1729_;
}
}
default: 
{
lean_object* v___x_1739_; 
v___x_1739_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1676_, v_post_1678_, v_usedLetOnly_1679_, v_skipConstInApp_1680_, v_skipInstances_1681_, v___y_1701_, v___y_1682_, v_snd_1696_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1739_;
}
}
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v_post_1678_);
lean_dec_ref(v_e_1677_);
lean_dec_ref(v_pre_1676_);
v_a_1753_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1690_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1690_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v___y_1683_);
lean_dec_ref(v_post_1678_);
lean_dec_ref(v_e_1677_);
lean_dec_ref(v_pre_1676_);
v_a_1761_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1689_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1689_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1769_, lean_object* v_pre_1770_, lean_object* v_e_1771_, lean_object* v_post_1772_, lean_object* v_usedLetOnly_1773_, lean_object* v_skipConstInApp_1774_, lean_object* v_skipInstances_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
uint8_t v_usedLetOnly_boxed_1783_; uint8_t v_skipConstInApp_boxed_1784_; uint8_t v_skipInstances_boxed_1785_; lean_object* v_res_1786_; 
v_usedLetOnly_boxed_1783_ = lean_unbox(v_usedLetOnly_1773_);
v_skipConstInApp_boxed_1784_ = lean_unbox(v_skipConstInApp_1774_);
v_skipInstances_boxed_1785_ = lean_unbox(v_skipInstances_1775_);
v_res_1786_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1769_, v_pre_1770_, v_e_1771_, v_post_1772_, v_usedLetOnly_boxed_1783_, v_skipConstInApp_boxed_1784_, v_skipInstances_boxed_1785_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1776_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1787_, lean_object* v_post_1788_, uint8_t v_usedLetOnly_1789_, uint8_t v_skipConstInApp_1790_, uint8_t v_skipInstances_1791_, lean_object* v_e_1792_, lean_object* v_a_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_inc(v_a_1793_);
v___x_1800_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1800_, 0, lean_box(0));
lean_closure_set(v___x_1800_, 1, lean_box(0));
lean_closure_set(v___x_1800_, 2, v_a_1793_);
v___x_1801_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1800_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1856_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1856_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1856_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_fst_1806_; lean_object* v_snd_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1855_; 
v_fst_1806_ = lean_ctor_get(v_a_1802_, 0);
v_snd_1807_ = lean_ctor_get(v_a_1802_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_a_1802_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1809_ = v_a_1802_;
v_isShared_1810_ = v_isSharedCheck_1855_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_snd_1807_);
lean_inc(v_fst_1806_);
lean_dec(v_a_1802_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1855_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_fst_1806_, v_e_1792_);
lean_dec(v_fst_1806_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___f_1816_; lean_object* v___x_1817_; 
lean_del_object(v___x_1809_);
lean_del_object(v___x_1804_);
v___x_1812_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1813_ = lean_box(v_usedLetOnly_1789_);
v___x_1814_ = lean_box(v_skipConstInApp_1790_);
v___x_1815_ = lean_box(v_skipInstances_1791_);
lean_inc_ref(v_e_1792_);
v___f_1816_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1816_, 0, v___x_1812_);
lean_closure_set(v___f_1816_, 1, v_pre_1787_);
lean_closure_set(v___f_1816_, 2, v_e_1792_);
lean_closure_set(v___f_1816_, 3, v_post_1788_);
lean_closure_set(v___f_1816_, 4, v___x_1813_);
lean_closure_set(v___f_1816_, 5, v___x_1814_);
lean_closure_set(v___f_1816_, 6, v___x_1815_);
v___x_1817_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___f_1816_, v_a_1793_, v_snd_1807_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v_fst_1819_; lean_object* v_snd_1820_; lean_object* v___f_1821_; lean_object* v___x_1822_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1817_, 1);
v_fst_1819_ = lean_ctor_get(v_a_1818_, 0);
lean_inc_n(v_fst_1819_, 2);
v_snd_1820_ = lean_ctor_get(v_a_1818_, 1);
lean_inc(v_snd_1820_);
lean_dec(v_a_1818_);
lean_inc(v_a_1793_);
v___f_1821_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1821_, 0, v_a_1793_);
lean_closure_set(v___f_1821_, 1, v_e_1792_);
lean_closure_set(v___f_1821_, 2, v_fst_1819_);
v___x_1822_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1821_, v_snd_1820_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1839_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1839_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1839_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_snd_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1837_; 
v_snd_1827_ = lean_ctor_get(v_a_1823_, 1);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_a_1823_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v_a_1823_, 0);
lean_dec(v_unused_1838_);
v___x_1829_ = v_a_1823_;
v_isShared_1830_ = v_isSharedCheck_1837_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snd_1827_);
lean_dec(v_a_1823_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1837_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v_fst_1819_);
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_fst_1819_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_snd_1827_);
v___x_1832_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1832_);
v___x_1834_ = v___x_1825_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_fst_1819_);
v_a_1840_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1822_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1822_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
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
else
{
lean_dec_ref(v_e_1792_);
return v___x_1817_;
}
}
else
{
lean_object* v_val_1848_; lean_object* v___x_1850_; 
lean_dec_ref(v_e_1792_);
lean_dec_ref(v_post_1788_);
lean_dec_ref(v_pre_1787_);
v_val_1848_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_val_1848_);
lean_dec_ref_known(v___x_1811_, 1);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v_val_1848_);
v___x_1850_ = v___x_1809_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_val_1848_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_snd_1807_);
v___x_1850_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1852_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1850_);
v___x_1852_ = v___x_1804_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v_e_1792_);
lean_dec_ref(v_post_1788_);
lean_dec_ref(v_pre_1787_);
v_a_1857_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1801_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1801_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1865_, lean_object* v_post_1866_, uint8_t v_usedLetOnly_1867_, uint8_t v_skipConstInApp_1868_, uint8_t v_skipInstances_1869_, lean_object* v_fvars_1870_, lean_object* v_e_1871_, lean_object* v_a_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
if (lean_obj_tag(v_e_1871_) == 7)
{
lean_object* v_binderName_1879_; lean_object* v_binderType_1880_; lean_object* v_body_1881_; uint8_t v_binderInfo_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___f_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_binderName_1879_ = lean_ctor_get(v_e_1871_, 0);
lean_inc(v_binderName_1879_);
v_binderType_1880_ = lean_ctor_get(v_e_1871_, 1);
lean_inc_ref(v_binderType_1880_);
v_body_1881_ = lean_ctor_get(v_e_1871_, 2);
lean_inc_ref(v_body_1881_);
v_binderInfo_1882_ = lean_ctor_get_uint8(v_e_1871_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1871_, 3);
v___x_1883_ = lean_box(v_usedLetOnly_1867_);
v___x_1884_ = lean_box(v_skipConstInApp_1868_);
v___x_1885_ = lean_box(v_skipInstances_1869_);
lean_inc_ref(v_post_1866_);
lean_inc_ref(v_pre_1865_);
lean_inc_ref(v_fvars_1870_);
v___f_1886_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1886_, 0, v_fvars_1870_);
lean_closure_set(v___f_1886_, 1, v_pre_1865_);
lean_closure_set(v___f_1886_, 2, v_post_1866_);
lean_closure_set(v___f_1886_, 3, v___x_1883_);
lean_closure_set(v___f_1886_, 4, v___x_1884_);
lean_closure_set(v___f_1886_, 5, v___x_1885_);
lean_closure_set(v___f_1886_, 6, v_body_1881_);
v___x_1887_ = lean_expr_instantiate_rev(v_binderType_1880_, v_fvars_1870_);
lean_dec_ref(v_fvars_1870_);
lean_dec_ref(v_binderType_1880_);
v___x_1888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1865_, v_post_1866_, v_usedLetOnly_1867_, v_skipConstInApp_1868_, v_skipInstances_1869_, v___x_1887_, v_a_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v_fst_1890_; lean_object* v_snd_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v_fst_1890_ = lean_ctor_get(v_a_1889_, 0);
lean_inc(v_fst_1890_);
v_snd_1891_ = lean_ctor_get(v_a_1889_, 1);
lean_inc(v_snd_1891_);
lean_dec(v_a_1889_);
v___x_1892_ = 0;
v___x_1893_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_binderName_1879_, v_binderInfo_1882_, v_fst_1890_, v___f_1886_, v___x_1892_, v_a_1872_, v_snd_1891_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1893_;
}
else
{
lean_dec_ref(v___f_1886_);
lean_dec(v_binderName_1879_);
return v___x_1888_;
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_expr_instantiate_rev(v_e_1871_, v_fvars_1870_);
lean_dec_ref(v_e_1871_);
lean_inc_ref(v_post_1866_);
lean_inc_ref(v_pre_1865_);
v___x_1895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1865_, v_post_1866_, v_usedLetOnly_1867_, v_skipConstInApp_1868_, v_skipInstances_1869_, v___x_1894_, v_a_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v_fst_1897_; lean_object* v_snd_1898_; uint8_t v___x_1899_; uint8_t v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v_fst_1897_ = lean_ctor_get(v_a_1896_, 0);
lean_inc(v_fst_1897_);
v_snd_1898_ = lean_ctor_get(v_a_1896_, 1);
lean_inc(v_snd_1898_);
lean_dec(v_a_1896_);
v___x_1899_ = 0;
v___x_1900_ = 1;
v___x_1901_ = 1;
v___x_1902_ = l_Lean_Meta_mkForallFVars(v_fvars_1870_, v_fst_1897_, v___x_1899_, v_usedLetOnly_1867_, v___x_1900_, v___x_1901_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec_ref(v_fvars_1870_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1865_, v_post_1866_, v_usedLetOnly_1867_, v_skipConstInApp_1868_, v_skipInstances_1869_, v_a_1903_, v_a_1872_, v_snd_1898_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1904_;
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v_snd_1898_);
lean_dec_ref(v_post_1866_);
lean_dec_ref(v_pre_1865_);
v_a_1905_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1902_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1902_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1870_);
lean_dec_ref(v_post_1866_);
lean_dec_ref(v_pre_1865_);
return v___x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1913_, lean_object* v_pre_1914_, lean_object* v_post_1915_, uint8_t v_usedLetOnly_1916_, uint8_t v_skipConstInApp_1917_, uint8_t v_skipInstances_1918_, lean_object* v_body_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_array_push(v_fvars_1913_, v_x_1920_);
v___x_1929_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1914_, v_post_1915_, v_usedLetOnly_1916_, v_skipConstInApp_1917_, v_skipInstances_1918_, v___x_1928_, v_body_1919_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1930_, lean_object* v_post_1931_, lean_object* v_usedLetOnly_1932_, lean_object* v_skipConstInApp_1933_, lean_object* v_skipInstances_1934_, lean_object* v_sz_1935_, lean_object* v_i_1936_, lean_object* v_bs_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
uint8_t v_usedLetOnly_boxed_1945_; uint8_t v_skipConstInApp_boxed_1946_; uint8_t v_skipInstances_boxed_1947_; size_t v_sz_boxed_1948_; size_t v_i_boxed_1949_; lean_object* v_res_1950_; 
v_usedLetOnly_boxed_1945_ = lean_unbox(v_usedLetOnly_1932_);
v_skipConstInApp_boxed_1946_ = lean_unbox(v_skipConstInApp_1933_);
v_skipInstances_boxed_1947_ = lean_unbox(v_skipInstances_1934_);
v_sz_boxed_1948_ = lean_unbox_usize(v_sz_1935_);
lean_dec(v_sz_1935_);
v_i_boxed_1949_ = lean_unbox_usize(v_i_1936_);
lean_dec(v_i_1936_);
v_res_1950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1930_, v_post_1931_, v_usedLetOnly_boxed_1945_, v_skipConstInApp_boxed_1946_, v_skipInstances_boxed_1947_, v_sz_boxed_1948_, v_i_boxed_1949_, v_bs_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1938_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object* v_pre_1951_, lean_object* v_post_1952_, lean_object* v_usedLetOnly_1953_, lean_object* v_skipConstInApp_1954_, lean_object* v_skipInstances_1955_, lean_object* v_e_1956_, lean_object* v_a_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
uint8_t v_usedLetOnly_boxed_1964_; uint8_t v_skipConstInApp_boxed_1965_; uint8_t v_skipInstances_boxed_1966_; lean_object* v_res_1967_; 
v_usedLetOnly_boxed_1964_ = lean_unbox(v_usedLetOnly_1953_);
v_skipConstInApp_boxed_1965_ = lean_unbox(v_skipConstInApp_1954_);
v_skipInstances_boxed_1966_ = lean_unbox(v_skipInstances_1955_);
v_res_1967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1951_, v_post_1952_, v_usedLetOnly_boxed_1964_, v_skipConstInApp_boxed_1965_, v_skipInstances_boxed_1966_, v_e_1956_, v_a_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v_a_1957_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1968_, lean_object* v_post_1969_, lean_object* v_usedLetOnly_1970_, lean_object* v_skipConstInApp_1971_, lean_object* v_skipInstances_1972_, lean_object* v_fvars_1973_, lean_object* v_e_1974_, lean_object* v_a_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v_usedLetOnly_boxed_1982_; uint8_t v_skipConstInApp_boxed_1983_; uint8_t v_skipInstances_boxed_1984_; lean_object* v_res_1985_; 
v_usedLetOnly_boxed_1982_ = lean_unbox(v_usedLetOnly_1970_);
v_skipConstInApp_boxed_1983_ = lean_unbox(v_skipConstInApp_1971_);
v_skipInstances_boxed_1984_ = lean_unbox(v_skipInstances_1972_);
v_res_1985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1968_, v_post_1969_, v_usedLetOnly_boxed_1982_, v_skipConstInApp_boxed_1983_, v_skipInstances_boxed_1984_, v_fvars_1973_, v_e_1974_, v_a_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v_a_1975_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1986_, lean_object* v_post_1987_, lean_object* v_usedLetOnly_1988_, lean_object* v_skipConstInApp_1989_, lean_object* v_skipInstances_1990_, lean_object* v_fvars_1991_, lean_object* v_e_1992_, lean_object* v_a_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
uint8_t v_usedLetOnly_boxed_2000_; uint8_t v_skipConstInApp_boxed_2001_; uint8_t v_skipInstances_boxed_2002_; lean_object* v_res_2003_; 
v_usedLetOnly_boxed_2000_ = lean_unbox(v_usedLetOnly_1988_);
v_skipConstInApp_boxed_2001_ = lean_unbox(v_skipConstInApp_1989_);
v_skipInstances_boxed_2002_ = lean_unbox(v_skipInstances_1990_);
v_res_2003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1986_, v_post_1987_, v_usedLetOnly_boxed_2000_, v_skipConstInApp_boxed_2001_, v_skipInstances_boxed_2002_, v_fvars_1991_, v_e_1992_, v_a_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v_a_1993_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_2004_, lean_object* v_post_2005_, lean_object* v_usedLetOnly_2006_, lean_object* v_skipConstInApp_2007_, lean_object* v_skipInstances_2008_, lean_object* v_e_2009_, lean_object* v_a_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v_usedLetOnly_boxed_2017_; uint8_t v_skipConstInApp_boxed_2018_; uint8_t v_skipInstances_boxed_2019_; lean_object* v_res_2020_; 
v_usedLetOnly_boxed_2017_ = lean_unbox(v_usedLetOnly_2006_);
v_skipConstInApp_boxed_2018_ = lean_unbox(v_skipConstInApp_2007_);
v_skipInstances_boxed_2019_ = lean_unbox(v_skipInstances_2008_);
v_res_2020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2004_, v_post_2005_, v_usedLetOnly_boxed_2017_, v_skipConstInApp_boxed_2018_, v_skipInstances_boxed_2019_, v_e_2009_, v_a_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v_a_2010_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_pre_2021_, lean_object* v_post_2022_, lean_object* v_usedLetOnly_2023_, lean_object* v_skipConstInApp_2024_, lean_object* v_skipInstances_2025_, lean_object* v_fvars_2026_, lean_object* v_e_2027_, lean_object* v_a_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_usedLetOnly_boxed_2035_; uint8_t v_skipConstInApp_boxed_2036_; uint8_t v_skipInstances_boxed_2037_; lean_object* v_res_2038_; 
v_usedLetOnly_boxed_2035_ = lean_unbox(v_usedLetOnly_2023_);
v_skipConstInApp_boxed_2036_ = lean_unbox(v_skipConstInApp_2024_);
v_skipInstances_boxed_2037_ = lean_unbox(v_skipInstances_2025_);
v_res_2038_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_2021_, v_post_2022_, v_usedLetOnly_boxed_2035_, v_skipConstInApp_boxed_2036_, v_skipInstances_boxed_2037_, v_fvars_2026_, v_e_2027_, v_a_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v_a_2028_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_upperBound_2039_, lean_object* v___x_2040_, lean_object* v_pre_2041_, lean_object* v_post_2042_, lean_object* v_usedLetOnly_2043_, lean_object* v_skipConstInApp_2044_, lean_object* v_skipInstances_2045_, lean_object* v_a_2046_, lean_object* v_b_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
uint8_t v_usedLetOnly_boxed_2055_; uint8_t v_skipConstInApp_boxed_2056_; uint8_t v_skipInstances_boxed_2057_; lean_object* v_res_2058_; 
v_usedLetOnly_boxed_2055_ = lean_unbox(v_usedLetOnly_2043_);
v_skipConstInApp_boxed_2056_ = lean_unbox(v_skipConstInApp_2044_);
v_skipInstances_boxed_2057_ = lean_unbox(v_skipInstances_2045_);
v_res_2058_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_upperBound_2039_, v___x_2040_, v_pre_2041_, v_post_2042_, v_usedLetOnly_boxed_2055_, v_skipConstInApp_boxed_2056_, v_skipInstances_boxed_2057_, v_a_2046_, v_b_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2048_);
lean_dec_ref(v___x_2040_);
lean_dec(v_upperBound_2039_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_skipInstances_2059_, lean_object* v_pre_2060_, lean_object* v_post_2061_, lean_object* v_usedLetOnly_2062_, lean_object* v_skipConstInApp_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
uint8_t v_skipInstances_boxed_2074_; uint8_t v_usedLetOnly_boxed_2075_; uint8_t v_skipConstInApp_boxed_2076_; lean_object* v_res_2077_; 
v_skipInstances_boxed_2074_ = lean_unbox(v_skipInstances_2059_);
v_usedLetOnly_boxed_2075_ = lean_unbox(v_usedLetOnly_2062_);
v_skipConstInApp_boxed_2076_ = lean_unbox(v_skipConstInApp_2063_);
v_res_2077_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_skipInstances_boxed_2074_, v_pre_2060_, v_post_2061_, v_usedLetOnly_boxed_2075_, v_skipConstInApp_boxed_2076_, v_x_2064_, v_x_2065_, v_x_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2067_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2078_, lean_object* v_x_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_apply_1(v_x_2079_, lean_box(0));
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___y_2080_);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2089_, lean_object* v_x_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2089_, v_x_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
return v_res_2097_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_unsigned_to_nat(16u);
v___x_2100_ = lean_mk_array(v___x_2099_, v___x_2098_);
return v___x_2100_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2102_ = lean_unsigned_to_nat(0u);
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v___x_2101_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2105_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2105_, 0, lean_box(0));
lean_closure_set(v___x_2105_, 1, lean_box(0));
lean_closure_set(v___x_2105_, 2, v___x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2106_, lean_object* v_pre_2107_, lean_object* v_post_2108_, uint8_t v_usedLetOnly_2109_, uint8_t v_skipConstInApp_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
uint8_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_a_2120_; lean_object* v_fst_2121_; lean_object* v_snd_2122_; lean_object* v___x_2123_; 
v___x_2117_ = 0;
v___x_2118_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2119_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2118_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref(v___x_2119_);
v_fst_2121_ = lean_ctor_get(v_a_2120_, 0);
lean_inc(v_fst_2121_);
v_snd_2122_ = lean_ctor_get(v_a_2120_, 1);
lean_inc(v_snd_2122_);
lean_dec(v_a_2120_);
v___x_2123_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2107_, v_post_2108_, v_usedLetOnly_2109_, v_skipConstInApp_2110_, v___x_2117_, v_input_2106_, v_fst_2121_, v_snd_2122_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v_fst_2125_; lean_object* v_snd_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2145_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v_fst_2125_ = lean_ctor_get(v_a_2124_, 0);
lean_inc(v_fst_2125_);
v_snd_2126_ = lean_ctor_get(v_a_2124_, 1);
lean_inc(v_snd_2126_);
lean_dec(v_a_2124_);
v___x_2127_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2127_, 0, lean_box(0));
lean_closure_set(v___x_2127_, 1, lean_box(0));
lean_closure_set(v___x_2127_, 2, v_fst_2121_);
v___x_2128_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2127_, v_snd_2126_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2145_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2145_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v_snd_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2143_; 
v_snd_2133_ = lean_ctor_get(v_a_2129_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_a_2129_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v_a_2129_, 0);
lean_dec(v_unused_2144_);
v___x_2135_ = v_a_2129_;
v_isShared_2136_ = v_isSharedCheck_2143_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_snd_2133_);
lean_dec(v_a_2129_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2143_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v_fst_2125_);
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_fst_2125_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_snd_2133_);
v___x_2138_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2138_);
v___x_2140_ = v___x_2131_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
else
{
lean_dec(v_fst_2121_);
return v___x_2123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2146_, lean_object* v_pre_2147_, lean_object* v_post_2148_, lean_object* v_usedLetOnly_2149_, lean_object* v_skipConstInApp_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v_usedLetOnly_boxed_2157_; uint8_t v_skipConstInApp_boxed_2158_; lean_object* v_res_2159_; 
v_usedLetOnly_boxed_2157_ = lean_unbox(v_usedLetOnly_2149_);
v_skipConstInApp_boxed_2158_ = lean_unbox(v_skipConstInApp_2150_);
v_res_2159_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2146_, v_pre_2147_, v_post_2148_, v_usedLetOnly_boxed_2157_, v_skipConstInApp_boxed_2158_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v___y_2169_; lean_object* v___x_2186_; uint8_t v_transparency_2187_; lean_object* v___f_2188_; lean_object* v___f_2189_; uint8_t v___x_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2186_ = l_Lean_Meta_Context_config(v_a_2163_);
v_transparency_2187_ = lean_ctor_get_uint8(v___x_2186_, 9);
lean_dec_ref(v___x_2186_);
v___f_2188_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2189_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2190_ = 0;
v___x_2191_ = 3;
v___x_2192_ = lean_box(0);
v___x_2193_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2187_, v___x_2191_);
if (v___x_2193_ == 0)
{
lean_object* v_keyedConfig_2194_; uint8_t v_trackZetaDelta_2195_; lean_object* v_zetaDeltaSet_2196_; lean_object* v_lctx_2197_; lean_object* v_localInstances_2198_; lean_object* v_defEqCtx_x3f_2199_; lean_object* v_synthPendingDepth_2200_; lean_object* v_customCanUnfoldPredicate_x3f_2201_; uint8_t v_univApprox_2202_; uint8_t v_inTypeClassResolution_2203_; uint8_t v_cacheInferType_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v_keyedConfig_2194_ = lean_ctor_get(v_a_2163_, 0);
v_trackZetaDelta_2195_ = lean_ctor_get_uint8(v_a_2163_, sizeof(void*)*7);
v_zetaDeltaSet_2196_ = lean_ctor_get(v_a_2163_, 1);
v_lctx_2197_ = lean_ctor_get(v_a_2163_, 2);
v_localInstances_2198_ = lean_ctor_get(v_a_2163_, 3);
v_defEqCtx_x3f_2199_ = lean_ctor_get(v_a_2163_, 4);
v_synthPendingDepth_2200_ = lean_ctor_get(v_a_2163_, 5);
v_customCanUnfoldPredicate_x3f_2201_ = lean_ctor_get(v_a_2163_, 6);
v_univApprox_2202_ = lean_ctor_get_uint8(v_a_2163_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2203_ = lean_ctor_get_uint8(v_a_2163_, sizeof(void*)*7 + 2);
v_cacheInferType_2204_ = lean_ctor_get_uint8(v_a_2163_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2194_);
v___x_2205_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2191_, v_keyedConfig_2194_);
lean_inc(v_customCanUnfoldPredicate_x3f_2201_);
lean_inc(v_synthPendingDepth_2200_);
lean_inc(v_defEqCtx_x3f_2199_);
lean_inc_ref(v_localInstances_2198_);
lean_inc_ref(v_lctx_2197_);
lean_inc(v_zetaDeltaSet_2196_);
v___x_2206_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v_zetaDeltaSet_2196_);
lean_ctor_set(v___x_2206_, 2, v_lctx_2197_);
lean_ctor_set(v___x_2206_, 3, v_localInstances_2198_);
lean_ctor_set(v___x_2206_, 4, v_defEqCtx_x3f_2199_);
lean_ctor_set(v___x_2206_, 5, v_synthPendingDepth_2200_);
lean_ctor_set(v___x_2206_, 6, v_customCanUnfoldPredicate_x3f_2201_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*7, v_trackZetaDelta_2195_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*7 + 1, v_univApprox_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*7 + 3, v_cacheInferType_2204_);
v___x_2207_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2162_, v___f_2189_, v___f_2188_, v___x_2190_, v___x_2190_, v___x_2192_, v___x_2206_, v_a_2164_, v_a_2165_, v_a_2166_);
lean_dec_ref_known(v___x_2206_, 7);
v___y_2169_ = v___x_2207_;
goto v___jp_2168_;
}
else
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2162_, v___f_2189_, v___f_2188_, v___x_2190_, v___x_2190_, v___x_2192_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
v___y_2169_ = v___x_2208_;
goto v___jp_2168_;
}
v___jp_2168_:
{
if (lean_obj_tag(v___y_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_a_2170_ = lean_ctor_get(v___y_2169_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___y_2169_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___y_2169_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___y_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_a_2178_ = lean_ctor_get(v___y_2169_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___y_2169_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___y_2169_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___y_2169_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Meta_expandCoe(v_e_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2216_, lean_object* v_m_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2217_, v_a_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2220_, lean_object* v_m_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2220_, v_m_2221_, v_a_2222_);
lean_dec(v_a_2222_);
lean_dec_ref(v_m_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_){
_start:
{
uint8_t v___x_2227_; 
v___x_2227_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2225_, v_x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_){
_start:
{
uint8_t v_res_2231_; lean_object* v_r_2232_; 
v_res_2231_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2228_, v_x_2229_, v_x_2230_);
lean_dec_ref(v_x_2230_);
lean_dec_ref(v_x_2229_);
v_r_2232_ = lean_box(v_res_2231_);
return v_r_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v___dummy_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg();
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2239_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2241_, lean_object* v_a_2242_, lean_object* v_x_2243_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(v_a_2242_, v_x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2245_, lean_object* v_a_2246_, lean_object* v_x_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6(v_00_u03b2_2245_, v_a_2246_, v_x_2247_);
lean_dec(v_x_2247_);
lean_dec(v_a_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_upperBound_2249_, lean_object* v___x_2250_, lean_object* v_pre_2251_, lean_object* v_post_2252_, uint8_t v_usedLetOnly_2253_, uint8_t v_skipConstInApp_2254_, uint8_t v_skipInstances_2255_, lean_object* v___x_2256_, lean_object* v_inst_2257_, lean_object* v_R_2258_, lean_object* v_a_2259_, lean_object* v_b_2260_, lean_object* v_c_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_upperBound_2249_, v___x_2250_, v_pre_2251_, v_post_2252_, v_usedLetOnly_2253_, v_skipConstInApp_2254_, v_skipInstances_2255_, v_a_2259_, v_b_2260_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object** _args){
lean_object* v_upperBound_2270_ = _args[0];
lean_object* v___x_2271_ = _args[1];
lean_object* v_pre_2272_ = _args[2];
lean_object* v_post_2273_ = _args[3];
lean_object* v_usedLetOnly_2274_ = _args[4];
lean_object* v_skipConstInApp_2275_ = _args[5];
lean_object* v_skipInstances_2276_ = _args[6];
lean_object* v___x_2277_ = _args[7];
lean_object* v_inst_2278_ = _args[8];
lean_object* v_R_2279_ = _args[9];
lean_object* v_a_2280_ = _args[10];
lean_object* v_b_2281_ = _args[11];
lean_object* v_c_2282_ = _args[12];
lean_object* v___y_2283_ = _args[13];
lean_object* v___y_2284_ = _args[14];
lean_object* v___y_2285_ = _args[15];
lean_object* v___y_2286_ = _args[16];
lean_object* v___y_2287_ = _args[17];
lean_object* v___y_2288_ = _args[18];
lean_object* v___y_2289_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2290_; uint8_t v_skipConstInApp_boxed_2291_; uint8_t v_skipInstances_boxed_2292_; lean_object* v_res_2293_; 
v_usedLetOnly_boxed_2290_ = lean_unbox(v_usedLetOnly_2274_);
v_skipConstInApp_boxed_2291_ = lean_unbox(v_skipConstInApp_2275_);
v_skipInstances_boxed_2292_ = lean_unbox(v_skipInstances_2276_);
v_res_2293_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_upperBound_2270_, v___x_2271_, v_pre_2272_, v_post_2273_, v_usedLetOnly_boxed_2290_, v_skipConstInApp_boxed_2291_, v_skipInstances_boxed_2292_, v___x_2277_, v_inst_2278_, v_R_2279_, v_a_2280_, v_b_2281_, v_c_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2283_);
lean_dec(v___x_2277_);
lean_dec_ref(v___x_2271_);
lean_dec(v_upperBound_2270_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_00_u03b2_2294_, lean_object* v_m_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_m_2295_, v_a_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_00_u03b2_2298_, lean_object* v_m_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_00_u03b2_2298_, v_m_2299_, v_a_2300_);
lean_dec_ref(v_a_2300_);
lean_dec_ref(v_m_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18(lean_object* v_00_u03b1_2302_, lean_object* v_name_2303_, uint8_t v_bi_2304_, lean_object* v_type_2305_, lean_object* v_k_2306_, uint8_t v_kind_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___redArg(v_name_2303_, v_bi_2304_, v_type_2305_, v_k_2306_, v_kind_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18___boxed(lean_object* v_00_u03b1_2316_, lean_object* v_name_2317_, lean_object* v_bi_2318_, lean_object* v_type_2319_, lean_object* v_k_2320_, lean_object* v_kind_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
uint8_t v_bi_boxed_2329_; uint8_t v_kind_boxed_2330_; lean_object* v_res_2331_; 
v_bi_boxed_2329_ = lean_unbox(v_bi_2318_);
v_kind_boxed_2330_ = lean_unbox(v_kind_2321_);
v_res_2331_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__18(v_00_u03b1_2316_, v_name_2317_, v_bi_boxed_2329_, v_type_2319_, v_k_2320_, v_kind_boxed_2330_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2322_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21(lean_object* v_00_u03b1_2332_, lean_object* v_name_2333_, lean_object* v_type_2334_, lean_object* v_val_2335_, lean_object* v_k_2336_, uint8_t v_nondep_2337_, uint8_t v_kind_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___redArg(v_name_2333_, v_type_2334_, v_val_2335_, v_k_2336_, v_nondep_2337_, v_kind_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21___boxed(lean_object* v_00_u03b1_2347_, lean_object* v_name_2348_, lean_object* v_type_2349_, lean_object* v_val_2350_, lean_object* v_k_2351_, lean_object* v_nondep_2352_, lean_object* v_kind_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
uint8_t v_nondep_boxed_2361_; uint8_t v_kind_boxed_2362_; lean_object* v_res_2363_; 
v_nondep_boxed_2361_ = lean_unbox(v_nondep_2352_);
v_kind_boxed_2362_ = lean_unbox(v_kind_2353_);
v_res_2363_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__21(v_00_u03b1_2347_, v_name_2348_, v_type_2349_, v_val_2350_, v_k_2351_, v_nondep_boxed_2361_, v_kind_boxed_2362_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2354_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b1_2364_, lean_object* v_ref_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_ref_2365_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b1_2372_, lean_object* v_ref_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b1_2372_, v_ref_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b1_2380_, lean_object* v_x_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_x_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___boxed(lean_object* v_00_u03b1_2390_, lean_object* v_x_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(v_00_u03b1_2390_, v_x_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2392_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18(lean_object* v_00_u03b2_2400_, lean_object* v_m_2401_, lean_object* v_a_2402_, lean_object* v_b_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v_m_2401_, v_a_2402_, v_b_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2405_, lean_object* v_x_2406_, size_t v_x_2407_, lean_object* v_x_2408_){
_start:
{
uint8_t v___x_2409_; 
v___x_2409_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2406_, v_x_2407_, v_x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2410_, lean_object* v_x_2411_, lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
size_t v_x_39702__boxed_2414_; uint8_t v_res_2415_; lean_object* v_r_2416_; 
v_x_39702__boxed_2414_ = lean_unbox_usize(v_x_2412_);
lean_dec(v_x_2412_);
v_res_2415_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2410_, v_x_2411_, v_x_39702__boxed_2414_, v_x_2413_);
lean_dec_ref(v_x_2413_);
lean_dec_ref(v_x_2411_);
v_r_2416_ = lean_box(v_res_2415_);
return v_r_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b2_2417_, lean_object* v_a_2418_, lean_object* v_x_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_a_2418_, v_x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b2_2421_, lean_object* v_a_2422_, lean_object* v_x_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b2_2421_, v_a_2422_, v_x_2423_);
lean_dec(v_x_2423_);
lean_dec_ref(v_a_2422_);
return v_res_2424_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26(lean_object* v_00_u03b2_2425_, lean_object* v_a_2426_, lean_object* v_x_2427_){
_start:
{
uint8_t v___x_2428_; 
v___x_2428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(v_a_2426_, v_x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___boxed(lean_object* v_00_u03b2_2429_, lean_object* v_a_2430_, lean_object* v_x_2431_){
_start:
{
uint8_t v_res_2432_; lean_object* v_r_2433_; 
v_res_2432_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26(v_00_u03b2_2429_, v_a_2430_, v_x_2431_);
lean_dec(v_x_2431_);
lean_dec_ref(v_a_2430_);
v_r_2433_ = lean_box(v_res_2432_);
return v_r_2433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27(lean_object* v_00_u03b2_2434_, lean_object* v_data_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_data_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28(lean_object* v_00_u03b2_2437_, lean_object* v_a_2438_, lean_object* v_b_2439_, lean_object* v_x_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__28___redArg(v_a_2438_, v_b_2439_, v_x_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2442_, lean_object* v_keys_2443_, lean_object* v_vals_2444_, lean_object* v_heq_2445_, lean_object* v_i_2446_, lean_object* v_k_2447_){
_start:
{
uint8_t v___x_2448_; 
v___x_2448_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2443_, v_i_2446_, v_k_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2449_, lean_object* v_keys_2450_, lean_object* v_vals_2451_, lean_object* v_heq_2452_, lean_object* v_i_2453_, lean_object* v_k_2454_){
_start:
{
uint8_t v_res_2455_; lean_object* v_r_2456_; 
v_res_2455_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2449_, v_keys_2450_, v_vals_2451_, v_heq_2452_, v_i_2453_, v_k_2454_);
lean_dec_ref(v_k_2454_);
lean_dec_ref(v_vals_2451_);
lean_dec_ref(v_keys_2450_);
v_r_2456_ = lean_box(v_res_2455_);
return v_r_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29(lean_object* v_00_u03b2_2457_, lean_object* v_i_2458_, lean_object* v_source_2459_, lean_object* v_target_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29___redArg(v_i_2458_, v_source_2459_, v_target_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30(lean_object* v_00_u03b2_2462_, lean_object* v_x_2463_, lean_object* v_x_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__29_spec__30___redArg(v_x_2463_, v_x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2466_, lean_object* v_decl_2467_, lean_object* v_ref_2468_){
_start:
{
lean_object* v_defValue_2470_; lean_object* v_descr_2471_; lean_object* v_deprecation_x3f_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_defValue_2470_ = lean_ctor_get(v_decl_2467_, 0);
v_descr_2471_ = lean_ctor_get(v_decl_2467_, 1);
v_deprecation_x3f_2472_ = lean_ctor_get(v_decl_2467_, 2);
v___x_2473_ = lean_alloc_ctor(1, 0, 1);
v___x_2474_ = lean_unbox(v_defValue_2470_);
lean_ctor_set_uint8(v___x_2473_, 0, v___x_2474_);
lean_inc(v_deprecation_x3f_2472_);
lean_inc_ref(v_descr_2471_);
lean_inc_n(v_name_2466_, 2);
v___x_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2475_, 0, v_name_2466_);
lean_ctor_set(v___x_2475_, 1, v_ref_2468_);
lean_ctor_set(v___x_2475_, 2, v___x_2473_);
lean_ctor_set(v___x_2475_, 3, v_descr_2471_);
lean_ctor_set(v___x_2475_, 4, v_deprecation_x3f_2472_);
v___x_2476_ = lean_register_option(v_name_2466_, v___x_2475_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2484_; 
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v___x_2476_, 0);
lean_dec(v_unused_2485_);
v___x_2478_ = v___x_2476_;
v_isShared_2479_ = v_isSharedCheck_2484_;
goto v_resetjp_2477_;
}
else
{
lean_dec(v___x_2476_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2484_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
lean_inc(v_defValue_2470_);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v_name_2466_);
lean_ctor_set(v___x_2480_, 1, v_defValue_2470_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v___x_2480_);
v___x_2482_ = v___x_2478_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v_name_2466_);
v_a_2486_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2476_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2476_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2494_, lean_object* v_decl_2495_, lean_object* v_ref_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2494_, v_decl_2495_, v_ref_2496_);
lean_dec_ref(v_decl_2495_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2513_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2514_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2515_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2516_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2513_, v___x_2514_, v___x_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_ref_2525_; lean_object* v___x_2526_; lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2535_; 
v_ref_2525_ = lean_ctor_get(v___y_2522_, 2);
v___x_2526_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__7(v_msg_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2529_ = v___x_2526_;
v_isShared_2530_ = v_isSharedCheck_2535_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2535_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2533_; 
lean_inc(v_ref_2525_);
v___x_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2531_, 0, v_ref_2525_);
lean_ctor_set(v___x_2531_, 1, v_a_2527_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set_tag(v___x_2529_, 1);
lean_ctor_set(v___x_2529_, 0, v___x_2531_);
v___x_2533_ = v___x_2529_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
return v_res_2542_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2551_ = l_Lean_stringToMessageData(v___x_2550_);
return v___x_2551_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
return v___x_2554_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2557_ = l_Lean_stringToMessageData(v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2558_, lean_object* v_expectedType_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v___x_2565_; 
lean_inc(v_a_2563_);
lean_inc_ref(v_a_2562_);
lean_inc(v_a_2561_);
lean_inc_ref(v_a_2560_);
lean_inc_ref(v_expr_2558_);
v___x_2565_ = lean_infer_type(v_expr_2558_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc_n(v_a_2566_, 2);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = l_Lean_Meta_getLevel(v_a_2566_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2567_, 1);
lean_inc_ref(v_expectedType_2559_);
v___x_2569_ = l_Lean_Meta_getLevel(v_expectedType_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2573_, 0, v_a_2570_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_a_2568_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
lean_inc_ref(v___x_2574_);
v___x_2575_ = l_Lean_mkConst(v___x_2571_, v___x_2574_);
v___x_2576_ = lean_unsigned_to_nat(3u);
v___x_2577_ = lean_mk_empty_array_with_capacity(v___x_2576_);
lean_inc(v_a_2566_);
v___x_2578_ = lean_array_push(v___x_2577_, v_a_2566_);
lean_inc_ref(v_expr_2558_);
v___x_2579_ = lean_array_push(v___x_2578_, v_expr_2558_);
lean_inc_ref(v_expectedType_2559_);
v___x_2580_ = lean_array_push(v___x_2579_, v_expectedType_2559_);
v___x_2581_ = l_Lean_mkAppN(v___x_2575_, v___x_2580_);
lean_dec_ref(v___x_2580_);
v___x_2582_ = lean_box(0);
v___x_2583_ = l_Lean_Meta_trySynthInstance(v___x_2581_, v___x_2582_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2681_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2681_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2681_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
switch(lean_obj_tag(v_a_2584_))
{
case 0:
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
lean_dec_ref_known(v___x_2574_, 2);
lean_dec(v_a_2566_);
lean_dec_ref(v_expectedType_2559_);
lean_dec_ref(v_expr_2558_);
v___x_2588_ = lean_box(0);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2588_);
v___x_2590_ = v___x_2586_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
case 1:
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2676_; 
lean_del_object(v___x_2586_);
v_a_2592_ = lean_ctor_get(v_a_2584_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v_a_2584_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2594_ = v_a_2584_;
v_isShared_2595_ = v_isSharedCheck_2676_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v_a_2584_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2676_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2596_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2597_ = l_Lean_mkConst(v___x_2596_, v___x_2574_);
v___x_2598_ = lean_unsigned_to_nat(4u);
v___x_2599_ = lean_mk_empty_array_with_capacity(v___x_2598_);
v___x_2600_ = lean_array_push(v___x_2599_, v_a_2566_);
lean_inc_ref(v_expr_2558_);
v___x_2601_ = lean_array_push(v___x_2600_, v_expr_2558_);
lean_inc_ref(v_expectedType_2559_);
v___x_2602_ = lean_array_push(v___x_2601_, v_expectedType_2559_);
v___x_2603_ = lean_array_push(v___x_2602_, v_a_2592_);
v___x_2604_ = l_Lean_mkAppN(v___x_2597_, v___x_2603_);
lean_dec_ref(v___x_2603_);
v___x_2605_ = l_Lean_Meta_expandCoe(v___x_2604_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2667_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2667_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2667_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_fst_2617_; lean_object* v___x_2618_; 
v_fst_2617_ = lean_ctor_get(v_a_2606_, 0);
lean_inc(v_a_2563_);
lean_inc_ref(v_a_2562_);
lean_inc(v_a_2561_);
lean_inc_ref(v_a_2560_);
lean_inc(v_fst_2617_);
v___x_2618_ = lean_infer_type(v_fst_2617_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2620_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
lean_inc_ref(v_expectedType_2559_);
v___x_2620_ = l_Lean_Meta_isExprDefEq(v_a_2619_, v_expectedType_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; uint8_t v___x_2622_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = lean_unbox(v_a_2621_);
lean_dec(v_a_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2648_; 
lean_inc(v_fst_2617_);
lean_del_object(v___x_2608_);
lean_del_object(v___x_2594_);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_a_2606_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; lean_object* v_unused_2650_; 
v_unused_2649_ = lean_ctor_get(v_a_2606_, 1);
lean_dec(v_unused_2649_);
v_unused_2650_ = lean_ctor_get(v_a_2606_, 0);
lean_dec(v_unused_2650_);
v___x_2624_ = v_a_2606_;
v_isShared_2625_ = v_isSharedCheck_2648_;
goto v_resetjp_2623_;
}
else
{
lean_dec(v_a_2606_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2648_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2626_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2627_ = l_Lean_indentExpr(v_expr_2558_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 7);
lean_ctor_set(v___x_2624_, 1, v___x_2627_);
lean_ctor_set(v___x_2624_, 0, v___x_2626_);
v___x_2629_ = v___x_2624_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
v___x_2630_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = l_Lean_indentExpr(v_expectedType_2559_);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_indentExpr(v_fst_2617_);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2637_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
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
else
{
lean_dec_ref(v_expectedType_2559_);
lean_dec_ref(v_expr_2558_);
goto v___jp_2610_;
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_del_object(v___x_2608_);
lean_dec(v_a_2606_);
lean_del_object(v___x_2594_);
lean_dec_ref(v_expectedType_2559_);
lean_dec_ref(v_expr_2558_);
v_a_2651_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2620_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2620_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
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
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_del_object(v___x_2608_);
lean_dec(v_a_2606_);
lean_del_object(v___x_2594_);
lean_dec_ref(v_expectedType_2559_);
lean_dec_ref(v_expr_2558_);
v_a_2659_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2618_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2618_);
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
v___jp_2610_:
{
lean_object* v___x_2612_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v_a_2606_);
v___x_2612_ = v___x_2594_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2606_);
v___x_2612_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2614_; 
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2612_);
v___x_2614_ = v___x_2608_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_del_object(v___x_2594_);
lean_dec_ref(v_expectedType_2559_);
lean_dec_ref(v_expr_2558_);
v_a_2668_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2605_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2605_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
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
default: 
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
lean_dec_ref_known(v___x_2574_, 2);
lean_dec(v_a_2566_);
lean_dec_ref(v_expectedType_2559_);
lean_dec_ref(v_expr_2558_);
v___x_2677_ = lean_box(2);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2677_);
v___x_2679_ = v___x_2586_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
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
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec_ref_known(v___x_2574_, 2);
lean_dec(v_a_2566_);
lean_dec_ref(v_expectedType_2559_);
lean_dec_ref(v_expr_2558_);
v_a_2682_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2583_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2583_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v_a_2568_);
lean_dec(v_a_2566_);
lean_dec_ref(v_expectedType_2559_);
lean_dec_ref(v_expr_2558_);
v_a_2690_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2569_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2569_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
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
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v_a_2566_);
lean_dec_ref(v_expectedType_2559_);
lean_dec_ref(v_expr_2558_);
v_a_2698_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2567_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2567_);
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
lean_dec_ref(v_expectedType_2559_);
lean_dec_ref(v_expr_2558_);
v_a_2706_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2565_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2565_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2714_, lean_object* v_expectedType_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2714_, v_expectedType_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2722_, lean_object* v_msg_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2730_, lean_object* v_msg_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2730_, v_msg_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2738_, lean_object* v_expectedType_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2738_, v_expectedType_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2770_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2770_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2770_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
switch(lean_obj_tag(v_a_2746_))
{
case 0:
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2750_ = lean_box(0);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2750_);
v___x_2752_ = v___x_2748_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
case 1:
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2765_; 
v_a_2754_ = lean_ctor_get(v_a_2746_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_a_2746_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2756_ = v_a_2746_;
v_isShared_2757_ = v_isSharedCheck_2765_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v_a_2746_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2765_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v_fst_2758_; lean_object* v___x_2760_; 
v_fst_2758_ = lean_ctor_get(v_a_2754_, 0);
lean_inc(v_fst_2758_);
lean_dec(v_a_2754_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v_fst_2758_);
v___x_2760_ = v___x_2756_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_fst_2758_);
v___x_2760_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2762_; 
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2760_);
v___x_2762_ = v___x_2748_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
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
default: 
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2766_ = lean_box(2);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2766_);
v___x_2768_ = v___x_2748_;
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
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
v_a_2771_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2745_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2745_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2779_, lean_object* v_expectedType_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2779_, v_expectedType_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
return v_res_2786_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2795_ = l_Lean_stringToMessageData(v___x_2794_);
return v___x_2795_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2798_ = l_Lean_stringToMessageData(v___x_2797_);
return v___x_2798_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2801_ = l_Lean_stringToMessageData(v___x_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___x_2808_; 
lean_inc(v_a_2806_);
lean_inc_ref(v_a_2805_);
lean_inc(v_a_2804_);
lean_inc_ref(v_a_2803_);
lean_inc_ref(v_expr_2802_);
v___x_2808_ = lean_infer_type(v_expr_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_n(v_a_2809_, 2);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = l_Lean_Meta_getLevel(v_a_2809_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___x_2812_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc_n(v_a_2813_, 2);
lean_dec_ref_known(v___x_2812_, 1);
v___x_2814_ = l_Lean_mkSort(v_a_2813_);
lean_inc(v_a_2809_);
v___x_2815_ = l_Lean_mkArrow(v_a_2809_, v___x_2814_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2817_, 0, v_a_2816_);
v___x_2818_ = 0;
v___x_2819_ = lean_box(0);
v___x_2820_ = l_Lean_Meta_mkFreshExprMVar(v___x_2817_, v___x_2818_, v___x_2819_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc_n(v_a_2821_, 2);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2824_, 0, v_a_2813_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2825_, 0, v_a_2811_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
lean_inc_ref(v___x_2825_);
v___x_2826_ = l_Lean_Expr_const___override(v___x_2822_, v___x_2825_);
lean_inc(v_a_2809_);
v___x_2827_ = l_Lean_mkAppB(v___x_2826_, v_a_2809_, v_a_2821_);
v___x_2828_ = lean_box(0);
v___x_2829_ = l_Lean_Meta_trySynthInstance(v___x_2827_, v___x_2828_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2916_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2916_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2916_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
if (lean_obj_tag(v_a_2830_) == 1)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2912_; 
lean_del_object(v___x_2832_);
v_a_2834_ = lean_ctor_get(v_a_2830_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_a_2830_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2836_ = v_a_2830_;
v_isShared_2837_ = v_isSharedCheck_2912_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v_a_2830_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2912_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2838_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2839_ = l_Lean_Expr_const___override(v___x_2838_, v___x_2825_);
lean_inc_ref(v_expr_2802_);
lean_inc(v_a_2834_);
v___x_2840_ = l_Lean_mkApp4(v___x_2839_, v_a_2809_, v_a_2821_, v_a_2834_, v_expr_2802_);
v___x_2841_ = l_Lean_Meta_expandCoe(v___x_2840_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2903_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2903_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2903_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_fst_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2901_; 
v_fst_2846_ = lean_ctor_get(v_a_2842_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_a_2842_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; 
v_unused_2902_ = lean_ctor_get(v_a_2842_, 1);
lean_dec(v_unused_2902_);
v___x_2848_ = v_a_2842_;
v_isShared_2849_ = v_isSharedCheck_2901_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_fst_2846_);
lean_dec(v_a_2842_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2901_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2857_; 
lean_inc(v_a_2806_);
lean_inc_ref(v_a_2805_);
lean_inc(v_a_2804_);
lean_inc_ref(v_a_2803_);
lean_inc(v_fst_2846_);
v___x_2857_ = lean_infer_type(v_fst_2846_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
lean_inc(v_a_2806_);
lean_inc_ref(v_a_2805_);
lean_inc(v_a_2804_);
lean_inc_ref(v_a_2803_);
v___x_2859_ = lean_whnf(v_a_2858_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; uint8_t v___x_2861_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v___x_2861_ = l_Lean_Expr_isForall(v_a_2860_);
lean_dec(v_a_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
lean_del_object(v___x_2844_);
lean_del_object(v___x_2836_);
v___x_2862_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2863_ = l_Lean_indentExpr(v_expr_2802_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set_tag(v___x_2848_, 7);
lean_ctor_set(v___x_2848_, 1, v___x_2863_);
lean_ctor_set(v___x_2848_, 0, v___x_2862_);
v___x_2865_ = v___x_2848_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
v___x_2866_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2865_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = l_Lean_indentExpr(v_fst_2846_);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2871_ = l_Lean_indentExpr(v_a_2834_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = l_Lean_MessageData_hint_x27(v___x_2872_);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2869_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2874_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
else
{
lean_del_object(v___x_2848_);
lean_dec(v_a_2834_);
lean_dec_ref(v_expr_2802_);
goto v___jp_2850_;
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_del_object(v___x_2848_);
lean_dec(v_fst_2846_);
lean_del_object(v___x_2844_);
lean_del_object(v___x_2836_);
lean_dec(v_a_2834_);
lean_dec_ref(v_expr_2802_);
v_a_2885_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2859_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2859_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_del_object(v___x_2848_);
lean_dec(v_fst_2846_);
lean_del_object(v___x_2844_);
lean_del_object(v___x_2836_);
lean_dec(v_a_2834_);
lean_dec_ref(v_expr_2802_);
v_a_2893_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2857_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2857_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
v___jp_2850_:
{
lean_object* v___x_2852_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v_fst_2846_);
v___x_2852_ = v___x_2836_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_fst_2846_);
v___x_2852_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2854_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2852_);
v___x_2854_ = v___x_2844_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
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
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_del_object(v___x_2836_);
lean_dec(v_a_2834_);
lean_dec_ref(v_expr_2802_);
v_a_2904_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2841_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2841_);
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
}
else
{
lean_object* v___x_2914_; 
lean_dec(v_a_2830_);
lean_dec_ref_known(v___x_2825_, 2);
lean_dec(v_a_2821_);
lean_dec(v_a_2809_);
lean_dec_ref(v_expr_2802_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v___x_2828_);
v___x_2914_ = v___x_2832_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2828_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref_known(v___x_2825_, 2);
lean_dec(v_a_2821_);
lean_dec(v_a_2809_);
lean_dec_ref(v_expr_2802_);
v_a_2917_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2829_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2829_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_a_2813_);
lean_dec(v_a_2811_);
lean_dec(v_a_2809_);
lean_dec_ref(v_expr_2802_);
v_a_2925_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2820_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2820_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
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
lean_dec(v_a_2813_);
lean_dec(v_a_2811_);
lean_dec(v_a_2809_);
lean_dec_ref(v_expr_2802_);
v_a_2933_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2815_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2815_);
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
lean_dec(v_a_2811_);
lean_dec(v_a_2809_);
lean_dec_ref(v_expr_2802_);
v_a_2941_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2812_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2812_);
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
lean_dec(v_a_2809_);
lean_dec_ref(v_expr_2802_);
v_a_2949_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2810_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2810_);
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
lean_dec_ref(v_expr_2802_);
v_a_2957_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2808_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2808_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
return v_res_2971_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2980_ = l_Lean_stringToMessageData(v___x_2979_);
return v___x_2980_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2983_ = l_Lean_stringToMessageData(v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___x_2990_; 
lean_inc(v_a_2988_);
lean_inc_ref(v_a_2987_);
lean_inc(v_a_2986_);
lean_inc_ref(v_a_2985_);
lean_inc_ref(v_expr_2984_);
v___x_2990_ = lean_infer_type(v_expr_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2992_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc_n(v_a_2991_, 2);
lean_dec_ref_known(v___x_2990_, 1);
v___x_2992_ = l_Lean_Meta_getLevel(v_a_2991_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2994_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v___x_2994_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc_n(v_a_2995_, 2);
lean_dec_ref_known(v___x_2994_, 1);
v___x_2996_ = l_Lean_mkSort(v_a_2995_);
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___x_2998_ = 0;
v___x_2999_ = lean_box(0);
v___x_3000_ = l_Lean_Meta_mkFreshExprMVar(v___x_2997_, v___x_2998_, v___x_2999_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc_n(v_a_3001_, 2);
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3004_, 0, v_a_2995_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3005_, 0, v_a_2993_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
lean_inc_ref(v___x_3005_);
v___x_3006_ = l_Lean_Expr_const___override(v___x_3002_, v___x_3005_);
lean_inc(v_a_2991_);
v___x_3007_ = l_Lean_mkAppB(v___x_3006_, v_a_2991_, v_a_3001_);
v___x_3008_ = lean_box(0);
v___x_3009_ = l_Lean_Meta_trySynthInstance(v___x_3007_, v___x_3008_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3096_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3096_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3096_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
if (lean_obj_tag(v_a_3010_) == 1)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3092_; 
lean_del_object(v___x_3012_);
v_a_3014_ = lean_ctor_get(v_a_3010_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_a_3010_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3016_ = v_a_3010_;
v_isShared_3017_ = v_isSharedCheck_3092_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v_a_3010_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3092_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3018_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_3019_ = l_Lean_Expr_const___override(v___x_3018_, v___x_3005_);
lean_inc_ref(v_expr_2984_);
lean_inc(v_a_3014_);
v___x_3020_ = l_Lean_mkApp4(v___x_3019_, v_a_2991_, v_a_3001_, v_a_3014_, v_expr_2984_);
v___x_3021_ = l_Lean_Meta_expandCoe(v___x_3020_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3083_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3083_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3083_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_fst_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3081_; 
v_fst_3026_ = lean_ctor_get(v_a_3022_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v_a_3022_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v_a_3022_, 1);
lean_dec(v_unused_3082_);
v___x_3028_ = v_a_3022_;
v_isShared_3029_ = v_isSharedCheck_3081_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_fst_3026_);
lean_dec(v_a_3022_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3081_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3037_; 
lean_inc(v_a_2988_);
lean_inc_ref(v_a_2987_);
lean_inc(v_a_2986_);
lean_inc_ref(v_a_2985_);
lean_inc(v_fst_3026_);
v___x_3037_ = lean_infer_type(v_fst_3026_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3039_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
lean_inc(v_a_2988_);
lean_inc_ref(v_a_2987_);
lean_inc(v_a_2986_);
lean_inc_ref(v_a_2985_);
v___x_3039_ = lean_whnf(v_a_3038_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; uint8_t v___x_3041_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___x_3039_, 1);
v___x_3041_ = l_Lean_Expr_isSort(v_a_3040_);
lean_dec(v_a_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
lean_del_object(v___x_3024_);
lean_del_object(v___x_3016_);
v___x_3042_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3043_ = l_Lean_indentExpr(v_expr_2984_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set_tag(v___x_3028_, 7);
lean_ctor_set(v___x_3028_, 1, v___x_3043_);
lean_ctor_set(v___x_3028_, 0, v___x_3042_);
v___x_3045_ = v___x_3028_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3042_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
v___x_3046_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = l_Lean_indentExpr(v_fst_3026_);
v___x_3049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
v___x_3050_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3051_ = l_Lean_indentExpr(v_a_3014_);
v___x_3052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3050_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = l_Lean_MessageData_hint_x27(v___x_3052_);
v___x_3054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3049_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3054_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_del_object(v___x_3028_);
lean_dec(v_a_3014_);
lean_dec_ref(v_expr_2984_);
goto v___jp_3030_;
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_del_object(v___x_3028_);
lean_dec(v_fst_3026_);
lean_del_object(v___x_3024_);
lean_del_object(v___x_3016_);
lean_dec(v_a_3014_);
lean_dec_ref(v_expr_2984_);
v_a_3065_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3039_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3039_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_del_object(v___x_3028_);
lean_dec(v_fst_3026_);
lean_del_object(v___x_3024_);
lean_del_object(v___x_3016_);
lean_dec(v_a_3014_);
lean_dec_ref(v_expr_2984_);
v_a_3073_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3037_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3037_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
v___jp_3030_:
{
lean_object* v___x_3032_; 
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v_fst_3026_);
v___x_3032_ = v___x_3016_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_fst_3026_);
v___x_3032_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3032_);
v___x_3034_ = v___x_3024_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
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
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_del_object(v___x_3016_);
lean_dec(v_a_3014_);
lean_dec_ref(v_expr_2984_);
v_a_3084_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3021_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3021_);
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
}
else
{
lean_object* v___x_3094_; 
lean_dec(v_a_3010_);
lean_dec_ref_known(v___x_3005_, 2);
lean_dec(v_a_3001_);
lean_dec(v_a_2991_);
lean_dec_ref(v_expr_2984_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3008_);
v___x_3094_ = v___x_3012_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3008_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref_known(v___x_3005_, 2);
lean_dec(v_a_3001_);
lean_dec(v_a_2991_);
lean_dec_ref(v_expr_2984_);
v_a_3097_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3009_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3009_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_a_2995_);
lean_dec(v_a_2993_);
lean_dec(v_a_2991_);
lean_dec_ref(v_expr_2984_);
v_a_3105_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3000_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3000_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
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
lean_dec(v_a_2993_);
lean_dec(v_a_2991_);
lean_dec_ref(v_expr_2984_);
v_a_3113_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_2994_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_2994_);
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
lean_dec(v_a_2991_);
lean_dec_ref(v_expr_2984_);
v_a_3121_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_2992_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_2992_);
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
lean_dec_ref(v_expr_2984_);
v_a_3129_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_2990_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_2990_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3144_, lean_object* v___y_3145_){
_start:
{
uint8_t v___x_3147_; 
v___x_3147_ = l_Lean_Expr_hasMVar(v_e_3144_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_e_3144_);
return v___x_3148_;
}
else
{
lean_object* v___x_3149_; lean_object* v_mctx_3150_; lean_object* v___x_3151_; lean_object* v_fst_3152_; lean_object* v_snd_3153_; lean_object* v___x_3154_; lean_object* v_cache_3155_; lean_object* v_zetaDeltaFVarIds_3156_; lean_object* v_postponed_3157_; lean_object* v_diag_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3167_; 
v___x_3149_ = lean_st_ref_get(v___y_3145_);
v_mctx_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc_ref(v_mctx_3150_);
lean_dec(v___x_3149_);
v___x_3151_ = l_Lean_instantiateMVarsCore(v_mctx_3150_, v_e_3144_);
v_fst_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_fst_3152_);
v_snd_3153_ = lean_ctor_get(v___x_3151_, 1);
lean_inc(v_snd_3153_);
lean_dec_ref(v___x_3151_);
v___x_3154_ = lean_st_ref_take(v___y_3145_);
v_cache_3155_ = lean_ctor_get(v___x_3154_, 1);
v_zetaDeltaFVarIds_3156_ = lean_ctor_get(v___x_3154_, 2);
v_postponed_3157_ = lean_ctor_get(v___x_3154_, 3);
v_diag_3158_ = lean_ctor_get(v___x_3154_, 4);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v___x_3154_, 0);
lean_dec(v_unused_3168_);
v___x_3160_ = v___x_3154_;
v_isShared_3161_ = v_isSharedCheck_3167_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_diag_3158_);
lean_inc(v_postponed_3157_);
lean_inc(v_zetaDeltaFVarIds_3156_);
lean_inc(v_cache_3155_);
lean_dec(v___x_3154_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3167_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v_snd_3153_);
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_snd_3153_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_cache_3155_);
lean_ctor_set(v_reuseFailAlloc_3166_, 2, v_zetaDeltaFVarIds_3156_);
lean_ctor_set(v_reuseFailAlloc_3166_, 3, v_postponed_3157_);
lean_ctor_set(v_reuseFailAlloc_3166_, 4, v_diag_3158_);
v___x_3163_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = lean_st_ref_put(v___y_3145_, v___x_3163_);
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v_fst_3152_);
return v___x_3165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3169_, v___y_3170_);
lean_dec(v___y_3170_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3173_, v___y_3175_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v___y_3194_; lean_object* v___x_3233_; uint8_t v_transparency_3234_; uint8_t v___x_3235_; uint8_t v___x_3236_; 
v___x_3233_ = l_Lean_Meta_Context_config(v_a_3188_);
v_transparency_3234_ = lean_ctor_get_uint8(v___x_3233_, 9);
lean_dec_ref(v___x_3233_);
v___x_3235_ = 2;
v___x_3236_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3234_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_object* v_keyedConfig_3237_; uint8_t v_trackZetaDelta_3238_; lean_object* v_zetaDeltaSet_3239_; lean_object* v_lctx_3240_; lean_object* v_localInstances_3241_; lean_object* v_defEqCtx_x3f_3242_; lean_object* v_synthPendingDepth_3243_; lean_object* v_customCanUnfoldPredicate_x3f_3244_; uint8_t v_univApprox_3245_; uint8_t v_inTypeClassResolution_3246_; uint8_t v_cacheInferType_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_keyedConfig_3237_ = lean_ctor_get(v_a_3188_, 0);
v_trackZetaDelta_3238_ = lean_ctor_get_uint8(v_a_3188_, sizeof(void*)*7);
v_zetaDeltaSet_3239_ = lean_ctor_get(v_a_3188_, 1);
v_lctx_3240_ = lean_ctor_get(v_a_3188_, 2);
v_localInstances_3241_ = lean_ctor_get(v_a_3188_, 3);
v_defEqCtx_x3f_3242_ = lean_ctor_get(v_a_3188_, 4);
v_synthPendingDepth_3243_ = lean_ctor_get(v_a_3188_, 5);
v_customCanUnfoldPredicate_x3f_3244_ = lean_ctor_get(v_a_3188_, 6);
v_univApprox_3245_ = lean_ctor_get_uint8(v_a_3188_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3246_ = lean_ctor_get_uint8(v_a_3188_, sizeof(void*)*7 + 2);
v_cacheInferType_3247_ = lean_ctor_get_uint8(v_a_3188_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3237_);
v___x_3248_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3235_, v_keyedConfig_3237_);
lean_inc(v_customCanUnfoldPredicate_x3f_3244_);
lean_inc(v_synthPendingDepth_3243_);
lean_inc(v_defEqCtx_x3f_3242_);
lean_inc_ref(v_localInstances_3241_);
lean_inc_ref(v_lctx_3240_);
lean_inc(v_zetaDeltaSet_3239_);
v___x_3249_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
lean_ctor_set(v___x_3249_, 1, v_zetaDeltaSet_3239_);
lean_ctor_set(v___x_3249_, 2, v_lctx_3240_);
lean_ctor_set(v___x_3249_, 3, v_localInstances_3241_);
lean_ctor_set(v___x_3249_, 4, v_defEqCtx_x3f_3242_);
lean_ctor_set(v___x_3249_, 5, v_synthPendingDepth_3243_);
lean_ctor_set(v___x_3249_, 6, v_customCanUnfoldPredicate_x3f_3244_);
lean_ctor_set_uint8(v___x_3249_, sizeof(void*)*7, v_trackZetaDelta_3238_);
lean_ctor_set_uint8(v___x_3249_, sizeof(void*)*7 + 1, v_univApprox_3245_);
lean_ctor_set_uint8(v___x_3249_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3246_);
lean_ctor_set_uint8(v___x_3249_, sizeof(void*)*7 + 3, v_cacheInferType_3247_);
lean_inc(v_a_3191_);
lean_inc_ref(v_a_3190_);
lean_inc(v_a_3189_);
v___x_3250_ = lean_whnf(v_type_3187_, v___x_3249_, v_a_3189_, v_a_3190_, v_a_3191_);
v___y_3194_ = v___x_3250_;
goto v___jp_3193_;
}
else
{
lean_object* v___x_3251_; 
lean_inc(v_a_3191_);
lean_inc_ref(v_a_3190_);
lean_inc(v_a_3189_);
lean_inc_ref(v_a_3188_);
v___x_3251_ = lean_whnf(v_type_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
v___y_3194_ = v___x_3251_;
goto v___jp_3193_;
}
v___jp_3193_:
{
if (lean_obj_tag(v___y_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3224_; 
v_a_3195_ = lean_ctor_get(v___y_3194_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___y_3194_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3197_ = v___y_3194_;
v_isShared_3198_ = v_isSharedCheck_3224_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___y_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3224_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
if (lean_obj_tag(v_a_3195_) == 5)
{
lean_object* v_fn_3199_; lean_object* v_arg_3200_; lean_object* v___x_3201_; lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3219_; 
lean_del_object(v___x_3197_);
v_fn_3199_ = lean_ctor_get(v_a_3195_, 0);
lean_inc_ref(v_fn_3199_);
v_arg_3200_ = lean_ctor_get(v_a_3195_, 1);
lean_inc_ref(v_arg_3200_);
lean_dec_ref_known(v_a_3195_, 2);
v___x_3201_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3199_, v_a_3189_);
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3219_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3219_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3218_; 
v___x_3206_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3200_, v_a_3189_);
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3209_ = v___x_3206_;
v_isShared_3210_ = v_isSharedCheck_3218_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3218_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v_a_3202_);
lean_ctor_set(v___x_3211_, 1, v_a_3207_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 1);
lean_ctor_set(v___x_3204_, 0, v___x_3211_);
v___x_3213_ = v___x_3204_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3215_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3213_);
v___x_3215_ = v___x_3209_;
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
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
lean_dec(v_a_3195_);
v___x_3220_ = lean_box(0);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3220_);
v___x_3222_ = v___x_3197_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
v_a_3225_ = lean_ctor_get(v___y_3194_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___y_3194_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___y_3194_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___y_3194_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
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
lean_dec_ref_known(v_a_3266_, 1);
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
lean_dec_ref_known(v_a_3273_, 1);
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
lean_dec_ref_known(v___x_3322_, 1);
if (lean_obj_tag(v_val_3324_) == 1)
{
uint8_t v_v_3325_; 
v_v_3325_ = lean_ctor_get_uint8(v_val_3324_, 0);
lean_dec_ref_known(v_val_3324_, 0);
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
lean_object* v_a_3378_; lean_object* v___y_3386_; lean_object* v___x_3396_; lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3800_; 
v___x_3396_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3371_, v_a_3373_);
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
v___jp_3377_:
{
uint8_t v___x_3379_; 
v___x_3379_ = l_Lean_Exception_isInterrupt(v_a_3378_);
if (v___x_3379_ == 0)
{
uint8_t v___x_3380_; 
lean_inc_ref(v_a_3378_);
v___x_3380_ = l_Lean_Exception_isRuntime(v_a_3378_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_dec_ref(v_a_3378_);
v___x_3381_ = lean_box(0);
v___x_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
return v___x_3382_;
}
else
{
lean_object* v___x_3383_; 
v___x_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3383_, 0, v_a_3378_);
return v___x_3383_;
}
}
else
{
lean_object* v___x_3384_; 
v___x_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_a_3378_);
return v___x_3384_;
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
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc_ref(v_e_3370_);
v___x_3401_ = lean_infer_type(v_e_3370_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3403_; lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3791_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3401_, 1);
v___x_3403_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3402_, v_a_3373_);
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
v___x_3408_ = l_Lean_Meta_isTypeApp_x3f(v_a_3397_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
v___x_3422_ = l_Lean_Meta_isTypeApp_x3f(v_a_3404_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
v___x_3436_ = l_Lean_Meta_saveState___redArg(v_a_3373_, v_a_3375_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3438_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3436_, 1);
lean_inc(v_fst_3417_);
lean_inc(v_fst_3431_);
v___x_3438_ = l_Lean_Meta_isExprDefEq(v_fst_3431_, v_fst_3417_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
lean_dec(v_a_3437_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3399_);
v___x_3444_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3374_);
v___x_3445_ = l_Lean_Meta_autoLift;
v___x_3446_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v___x_3444_, v___x_3445_);
lean_dec_ref(v___x_3444_);
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
lean_dec_ref(v_e_3370_);
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
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_fst_3431_);
v___x_3451_ = lean_infer_type(v_fst_3431_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3453_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
v___x_3453_ = lean_whnf(v_a_3452_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
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
lean_dec_ref_known(v_a_3454_, 3);
v_u_3457_ = lean_ctor_get(v_binderType_3455_, 0);
lean_inc(v_u_3457_);
lean_dec_ref_known(v_binderType_3455_, 1);
v_u_3458_ = lean_ctor_get(v_body_3456_, 0);
lean_inc(v_u_3458_);
lean_dec_ref_known(v_body_3456_, 1);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_fst_3417_);
v___x_3459_ = lean_infer_type(v_fst_3417_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
v___x_3461_ = lean_whnf(v_a_3460_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3461_, 1);
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
lean_dec_ref_known(v_a_3462_, 3);
v_u_3465_ = lean_ctor_get(v_binderType_3463_, 0);
lean_inc(v_u_3465_);
lean_dec_ref_known(v_binderType_3463_, 1);
v_u_3466_ = lean_ctor_get(v_body_3464_, 0);
lean_inc(v_u_3466_);
lean_dec_ref_known(v_body_3464_, 1);
v___x_3467_ = l_Lean_Meta_decLevel(v_u_3457_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v___x_3469_ = l_Lean_Meta_decLevel(v_u_3465_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3471_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
lean_inc(v_a_3468_);
v___x_3471_ = l_Lean_Meta_isLevelDefEq(v_a_3468_, v_a_3470_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
v___x_3477_ = l_Lean_Meta_decLevel(v_u_3458_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v___x_3479_ = l_Lean_Meta_decLevel(v_u_3466_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3484_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
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
v___x_3495_ = l_Lean_Meta_trySynthInstance(v___x_3493_, v___x_3494_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
lean_dec_ref_known(v_a_3496_, 1);
lean_inc(v_snd_3432_);
v___x_3501_ = l_Lean_Meta_getDecLevel(v_snd_3432_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = l_Lean_Meta_getDecLevel(v_a_3404_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
lean_inc(v_a_3397_);
v___x_3505_ = l_Lean_Meta_getDecLevel(v_a_3397_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
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
lean_inc_ref(v_e_3370_);
v___x_3518_ = lean_array_push(v___x_3517_, v_e_3370_);
v___x_3519_ = l_Lean_mkAppN(v___x_3511_, v___x_3518_);
lean_dec_ref(v___x_3518_);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc_ref(v___x_3519_);
v___x_3520_ = lean_infer_type(v___x_3519_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
lean_inc(v_a_3397_);
v___x_3522_ = l_Lean_Meta_isExprDefEq(v_a_3397_, v_a_3521_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
v___x_3528_ = l_Lean_Meta_isMonad_x3f(v_fst_3417_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
v___x_3537_ = l_Lean_Meta_getLevel(v_snd_3432_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3539_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref_known(v___x_3537_, 1);
lean_inc(v_snd_3418_);
v___x_3539_ = l_Lean_Meta_getLevel(v_snd_3418_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3539_, 1);
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
v___x_3555_ = l_Lean_Meta_trySynthInstance(v___x_3554_, v___x_3494_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
lean_dec_ref_known(v_a_3556_, 1);
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
v___x_3572_ = lean_array_push(v___x_3571_, v_e_3370_);
v___x_3573_ = l_Lean_mkAppN(v___x_3562_, v___x_3572_);
lean_dec_ref(v___x_3572_);
v___x_3574_ = l_Lean_Meta_expandCoe(v___x_3573_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v_fst_3576_; lean_object* v___x_3577_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3574_, 1);
v_fst_3576_ = lean_ctor_get(v_a_3575_, 0);
lean_inc_n(v_fst_3576_, 2);
lean_dec(v_a_3575_);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
v___x_3577_ = lean_infer_type(v_fst_3576_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3579_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v___x_3579_ = l_Lean_Meta_isExprDefEq(v_a_3397_, v_a_3578_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
lean_dec_ref_known(v___x_3579_, 1);
v_a_3378_ = v_a_3595_;
goto v___jp_3377_;
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
lean_dec_ref_known(v___x_3577_, 1);
v_a_3378_ = v_a_3596_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3597_; 
lean_del_object(v___x_3535_);
lean_dec(v_a_3397_);
v_a_3597_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3574_, 1);
v_a_3378_ = v_a_3597_;
goto v___jp_3377_;
}
}
else
{
lean_object* v___x_3599_; 
lean_dec(v_a_3556_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
lean_dec_ref_known(v___x_3510_, 2);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3370_);
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
lean_dec_ref_known(v___x_3510_, 2);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3370_);
v_a_3602_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3555_, 1);
v_a_3378_ = v_a_3602_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3603_; 
lean_dec(v_a_3538_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
lean_dec_ref_known(v___x_3510_, 2);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3370_);
v_a_3603_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3539_, 1);
v_a_3378_ = v_a_3603_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3604_; 
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
lean_dec_ref_known(v___x_3510_, 2);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3370_);
v_a_3604_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3537_, 1);
v_a_3378_ = v_a_3604_;
goto v___jp_3377_;
}
}
}
else
{
lean_object* v___x_3607_; 
lean_dec(v_a_3529_);
lean_dec_ref_known(v___x_3510_, 2);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3370_);
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
lean_dec_ref_known(v___x_3510_, 2);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3370_);
v_a_3610_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3528_, 1);
v_a_3378_ = v_a_3610_;
goto v___jp_3377_;
}
}
else
{
lean_object* v___x_3612_; 
lean_dec_ref_known(v___x_3510_, 2);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3370_);
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
lean_dec_ref_known(v___x_3510_, 2);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3370_);
v_a_3618_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3522_, 1);
v_a_3378_ = v_a_3618_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3619_; 
lean_dec_ref(v___x_3519_);
lean_dec_ref_known(v___x_3510_, 2);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3370_);
v_a_3619_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3520_, 1);
v_a_3378_ = v_a_3619_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v_a_3620_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3620_);
lean_dec_ref_known(v___x_3505_, 1);
v_a_3378_ = v_a_3620_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v_a_3621_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3503_, 1);
v_a_3378_ = v_a_3621_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v_a_3622_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3622_);
lean_dec_ref_known(v___x_3501_, 1);
v_a_3378_ = v_a_3622_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
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
lean_dec_ref(v_e_3370_);
v_a_3627_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3627_);
lean_dec_ref_known(v___x_3495_, 1);
v_a_3378_ = v_a_3627_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v_a_3630_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3479_, 1);
v_a_3378_ = v_a_3630_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v_a_3631_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3477_, 1);
v_a_3378_ = v_a_3631_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
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
lean_dec_ref(v_e_3370_);
v_a_3637_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3471_, 1);
v_a_3378_ = v_a_3637_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v_a_3638_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3469_, 1);
v_a_3378_ = v_a_3638_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v_a_3639_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3467_, 1);
v_a_3378_ = v_a_3639_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v___x_3640_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3462_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec_ref_known(v_a_3462_, 3);
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
lean_dec_ref(v_e_3370_);
v___x_3641_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3462_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec_ref_known(v_a_3462_, 3);
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
lean_dec_ref(v_e_3370_);
v___x_3642_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3462_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
lean_dec_ref(v_e_3370_);
v_a_3643_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___x_3461_, 1);
v_a_3378_ = v_a_3643_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v_a_3644_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3459_, 1);
v_a_3378_ = v_a_3644_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v___x_3645_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3454_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec_ref_known(v_a_3454_, 3);
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
lean_dec_ref(v_e_3370_);
v___x_3646_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3454_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec_ref_known(v_a_3454_, 3);
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
lean_dec_ref(v_e_3370_);
v___x_3647_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3454_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
lean_dec_ref(v_e_3370_);
v_a_3648_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3648_);
lean_dec_ref_known(v___x_3453_, 1);
v_a_3378_ = v_a_3648_;
goto v___jp_3377_;
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
lean_dec_ref(v_e_3370_);
v_a_3649_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3649_);
lean_dec_ref_known(v___x_3451_, 1);
v_a_3378_ = v_a_3649_;
goto v___jp_3377_;
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
v___x_3650_ = l_Lean_Meta_isMonad_x3f(v_fst_3417_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
lean_object* v___x_3662_; lean_object* v_a_3664_; lean_object* v___x_3691_; 
v___x_3662_ = lean_box(0);
if (v_isShared_3400_ == 0)
{
lean_ctor_set_tag(v___x_3399_, 1);
lean_ctor_set(v___x_3399_, 0, v_e_3370_);
v___x_3691_ = v___x_3399_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_e_3370_);
v___x_3691_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3690_;
}
v___jp_3663_:
{
uint8_t v___x_3665_; 
v___x_3665_ = l_Lean_Exception_isInterrupt(v_a_3664_);
if (v___x_3665_ == 0)
{
uint8_t v___x_3666_; 
lean_inc_ref(v_a_3664_);
v___x_3666_ = l_Lean_Exception_isRuntime(v_a_3664_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; 
lean_dec_ref(v_a_3664_);
lean_del_object(v___x_3653_);
v___x_3667_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3437_, v_a_3373_, v_a_3375_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3674_ == 0)
{
lean_object* v_unused_3675_; 
v_unused_3675_ = lean_ctor_get(v___x_3667_, 0);
lean_dec(v_unused_3675_);
v___x_3669_ = v___x_3667_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_dec(v___x_3667_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3662_);
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3662_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
v_a_3676_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3667_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3667_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
else
{
lean_object* v___x_3685_; 
lean_dec(v_a_3437_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set_tag(v___x_3653_, 1);
lean_ctor_set(v___x_3653_, 0, v_a_3664_);
v___x_3685_ = v___x_3653_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3664_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
else
{
lean_object* v___x_3688_; 
lean_dec(v_a_3437_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set_tag(v___x_3653_, 1);
lean_ctor_set(v___x_3653_, 0, v_a_3664_);
v___x_3688_ = v___x_3653_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3664_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
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
v___x_3700_ = l_Lean_Meta_mkAppOptM(v___x_3655_, v___x_3699_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
v___x_3705_ = l_Lean_Meta_expandCoe(v_a_3701_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
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
lean_dec_ref_known(v___x_3705_, 1);
v_a_3664_ = v_a_3718_;
goto v___jp_3663_;
}
}
}
else
{
lean_object* v_a_3720_; 
v_a_3720_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v___x_3700_, 1);
v_a_3664_ = v_a_3720_;
goto v___jp_3663_;
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
lean_dec_ref(v_e_3370_);
v___x_3725_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3437_, v_a_3373_, v_a_3375_);
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
lean_dec_ref(v_e_3370_);
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
lean_dec_ref(v_e_3370_);
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
lean_dec_ref(v_e_3370_);
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
lean_dec_ref(v_e_3370_);
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
lean_dec_ref(v_e_3370_);
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
lean_dec_ref(v_e_3370_);
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
lean_dec_ref(v_e_3370_);
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
lean_dec_ref(v_e_3370_);
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
lean_dec_ref_known(v___x_3834_, 1);
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
lean_dec_ref_known(v___x_3838_, 1);
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
lean_dec_ref_known(v___x_3844_, 1);
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
