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
lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_res_7_;
v_res_7_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(v_x_1_, v___y_2_, v___y_3_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object* v_x_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(v_x_8_, v___y_9_, v___y_10_);
lean_dec(v___y_10_);
lean_dec_ref(v___y_9_);
lean_dec(v_x_8_);
return v_res_12_;
}
}
lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; lean_object* v___x_33_; 
v___f_26_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_27_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_28_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_29_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_30_ = 0;
v___x_31_ = lean_box(2);
v___x_32_ = 0;
v___x_33_ = l_Lean_registerTagAttribute(v___x_27_, v___x_28_, v___f_26_, v___x_29_, v___x_30_, v___x_31_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_34_;
v_res_34_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
return v_res_36_;
}
}
lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1(){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_40_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0));
v___x_41_ = l_Lean_addBuiltinDocString(v___x_39_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_42_;
v_res_42_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___boxed(lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
return v_res_44_;
}
}
lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3(){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6));
v___x_73_ = l_Lean_addBuiltinDeclarationRanges(v___x_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_74_;
v_res_74_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___boxed(lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
return v_res_76_;
}
}
uint8_t l_Lean_Meta_isCoeDecl(lean_object* v_env_77_, lean_object* v_declName_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = l_Lean_Meta_coeDeclAttr;
v___x_80_ = l_Lean_TagAttribute_hasTag(v___x_79_, v_env_77_, v_declName_78_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Lean_Meta_isCoeDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_77_ = stack[0].m_obj;
lean_object* v_declName_78_ = stack[1].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Lean_Meta_isCoeDecl(v_env_77_, v_declName_78_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object* v_env_82_, lean_object* v_declName_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Lean_Meta_isCoeDecl(v_env_82_, v_declName_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(lean_object* v_declName_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_env_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = lean_st_ref_get(v___y_87_);
v_env_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc_ref(v_env_90_);
lean_dec(v___x_89_);
v___x_91_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_90_, v_declName_86_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_86_ = stack[0].m_obj;
lean_object* v___y_87_ = stack[1].m_obj;
lean_object* v_res_93_;
v_res_93_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_declName_86_, v___y_87_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg___boxed(lean_object* v_declName_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_declName_94_, v___y_95_);
lean_dec(v___y_95_);
return v_res_97_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0(lean_object* v_declName_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_declName_98_, v___y_102_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_98_ = stack[0].m_obj;
lean_object* v___y_99_ = stack[1].m_obj;
lean_object* v___y_100_ = stack[2].m_obj;
lean_object* v___y_101_ = stack[3].m_obj;
lean_object* v___y_102_ = stack[4].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0(v_declName_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___boxed(lean_object* v_declName_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0(v_declName_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_box(0);
v___x_114_ = l_Lean_Expr_sort___override(v___x_113_);
return v___x_114_;
}
}
lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(lean_object* v_e_115_, lean_object* v_nm_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v___x_122_; 
lean_inc(v_nm_116_);
v___x_122_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_nm_116_, v_a_120_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_145_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_145_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_145_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_145_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
if (lean_obj_tag(v_a_123_) == 1)
{
lean_object* v_val_127_; lean_object* v_numParams_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_val_127_ = lean_ctor_get(v_a_123_, 0);
lean_inc(v_val_127_);
lean_dec_ref_known(v_a_123_, 1);
v_numParams_128_ = lean_ctor_get(v_val_127_, 1);
lean_inc(v_numParams_128_);
lean_dec(v_val_127_);
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v___x_130_ = l_Lean_Expr_getAppNumArgs(v_e_115_);
v___x_131_ = lean_nat_sub(v___x_130_, v_numParams_128_);
lean_dec(v_numParams_128_);
lean_dec(v___x_130_);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_sub(v___x_131_, v___x_132_);
lean_dec(v___x_131_);
v___x_134_ = l_Lean_Expr_getRevArgD(v_e_115_, v___x_133_, v___x_129_);
lean_dec_ref(v_e_115_);
v___x_135_ = l_Lean_Expr_getAppFn(v___x_134_);
v___x_136_ = l_Lean_Expr_isConst(v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_138_; 
lean_dec_ref(v___x_135_);
lean_dec_ref(v___x_134_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v_nm_116_);
v___x_138_ = v___x_125_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_nm_116_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
else
{
lean_object* v___x_140_; 
lean_del_object(v___x_125_);
lean_dec(v_nm_116_);
v___x_140_ = l_Lean_Expr_constName_x21(v___x_135_);
lean_dec_ref(v___x_135_);
v_e_115_ = v___x_134_;
v_nm_116_ = v___x_140_;
goto _start;
}
}
else
{
lean_object* v___x_143_; 
lean_dec(v_a_123_);
lean_dec_ref(v_e_115_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v_nm_116_);
v___x_143_ = v___x_125_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_nm_116_);
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
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_nm_116_);
lean_dec_ref(v_e_115_);
v_a_146_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_122_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_122_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_115_ = stack[0].m_obj;
lean_object* v_nm_116_ = stack[1].m_obj;
lean_object* v_a_117_ = stack[2].m_obj;
lean_object* v_a_118_ = stack[3].m_obj;
lean_object* v_a_119_ = stack[4].m_obj;
lean_object* v_a_120_ = stack[5].m_obj;
lean_object* v_res_154_;
v_res_154_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_115_, v_nm_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___boxed(lean_object* v_e_155_, lean_object* v_nm_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_155_, v_nm_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
return v_res_162_;
}
}
lean_object* l_Lean_Meta_expandCoe___lam__0(lean_object* v_e_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v_e_163_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___y_164_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT void l_Lean_Meta_expandCoe___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_163_ = stack[0].m_obj;
lean_object* v___y_164_ = stack[1].m_obj;
lean_object* v___y_165_ = stack[2].m_obj;
lean_object* v___y_166_ = stack[3].m_obj;
lean_object* v___y_167_ = stack[4].m_obj;
lean_object* v___y_168_ = stack[5].m_obj;
lean_object* v_res_173_;
v_res_173_ = l_Lean_Meta_expandCoe___lam__0(v_e_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__0___boxed(lean_object* v_e_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Meta_expandCoe___lam__0(v_e_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___lam__0(lean_object* v___x_182_, lean_object* v_entry_183_, lean_object* v_s_184_){
_start:
{
lean_object* v_addEntryFn_185_; lean_object* v_importedEntries_186_; lean_object* v_state_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_195_; 
v_addEntryFn_185_ = lean_ctor_get(v___x_182_, 3);
lean_inc(v_addEntryFn_185_);
lean_dec_ref(v___x_182_);
v_importedEntries_186_ = lean_ctor_get(v_s_184_, 0);
v_state_187_ = lean_ctor_get(v_s_184_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_s_184_);
if (v_isSharedCheck_195_ == 0)
{
v___x_189_ = v_s_184_;
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_state_187_);
lean_inc(v_importedEntries_186_);
lean_dec(v_s_184_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_state_191_; lean_object* v___x_193_; 
v_state_191_ = lean_apply_2(v_addEntryFn_185_, v_state_187_, v_entry_183_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v_state_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_importedEntries_186_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_state_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(lean_object* v_msgData_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; lean_object* v_env_203_; uint8_t v___x_204_; lean_object* v_env_205_; lean_object* v___x_206_; lean_object* v_toCold_207_; lean_object* v_mctx_208_; lean_object* v_lctx_209_; lean_object* v_options_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_202_ = lean_st_ref_get(v___y_200_);
v_env_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc_ref(v_env_203_);
lean_dec(v___x_202_);
v___x_204_ = 0;
v_env_205_ = l_Lean_Environment_setRecordingDeps(v_env_203_, v___x_204_);
v___x_206_ = lean_st_ref_get(v___y_198_);
v_toCold_207_ = lean_ctor_get(v___y_199_, 0);
v_mctx_208_ = lean_ctor_get(v___x_206_, 0);
lean_inc_ref(v_mctx_208_);
lean_dec(v___x_206_);
v_lctx_209_ = lean_ctor_get(v___y_197_, 2);
v_options_210_ = lean_ctor_get(v_toCold_207_, 2);
lean_inc_ref(v_options_210_);
lean_inc_ref(v_lctx_209_);
v___x_211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_211_, 0, v_env_205_);
lean_ctor_set(v___x_211_, 1, v_mctx_208_);
lean_ctor_set(v___x_211_, 2, v_lctx_209_);
lean_ctor_set(v___x_211_, 3, v_options_210_);
v___x_212_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v_msgData_196_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_196_ = stack[0].m_obj;
lean_object* v___y_197_ = stack[1].m_obj;
lean_object* v___y_198_ = stack[2].m_obj;
lean_object* v___y_199_ = stack[3].m_obj;
lean_object* v___y_200_ = stack[4].m_obj;
lean_object* v_res_214_;
v_res_214_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msgData_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_msgData_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msgData_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_221_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_222_; double v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_float_of_nat(v___x_222_);
return v___x_223_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object* v_cls_227_, lean_object* v_msg_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_ref_235_; lean_object* v___x_236_; lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_283_; 
v_ref_235_ = lean_ctor_get(v___y_232_, 2);
v___x_236_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_228_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_283_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_283_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_283_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v_traceState_242_; lean_object* v_env_243_; lean_object* v_nextMacroScope_244_; lean_object* v_ngen_245_; lean_object* v_auxDeclNGen_246_; lean_object* v_cache_247_; lean_object* v_recordedDeps_248_; lean_object* v_messages_249_; lean_object* v_infoState_250_; lean_object* v_snapshotTasks_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_282_; 
v___x_241_ = lean_st_ref_take(v___y_233_);
v_traceState_242_ = lean_ctor_get(v___x_241_, 4);
v_env_243_ = lean_ctor_get(v___x_241_, 0);
v_nextMacroScope_244_ = lean_ctor_get(v___x_241_, 1);
v_ngen_245_ = lean_ctor_get(v___x_241_, 2);
v_auxDeclNGen_246_ = lean_ctor_get(v___x_241_, 3);
v_cache_247_ = lean_ctor_get(v___x_241_, 5);
v_recordedDeps_248_ = lean_ctor_get(v___x_241_, 6);
v_messages_249_ = lean_ctor_get(v___x_241_, 7);
v_infoState_250_ = lean_ctor_get(v___x_241_, 8);
v_snapshotTasks_251_ = lean_ctor_get(v___x_241_, 9);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_282_ == 0)
{
v___x_253_ = v___x_241_;
v_isShared_254_ = v_isSharedCheck_282_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_snapshotTasks_251_);
lean_inc(v_infoState_250_);
lean_inc(v_messages_249_);
lean_inc(v_recordedDeps_248_);
lean_inc(v_cache_247_);
lean_inc(v_traceState_242_);
lean_inc(v_auxDeclNGen_246_);
lean_inc(v_ngen_245_);
lean_inc(v_nextMacroScope_244_);
lean_inc(v_env_243_);
lean_dec(v___x_241_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_282_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
uint64_t v_tid_255_; lean_object* v_traces_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_281_; 
v_tid_255_ = lean_ctor_get_uint64(v_traceState_242_, sizeof(void*)*1);
v_traces_256_ = lean_ctor_get(v_traceState_242_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v_traceState_242_);
if (v_isSharedCheck_281_ == 0)
{
v___x_258_ = v_traceState_242_;
v_isShared_259_ = v_isSharedCheck_281_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_traces_256_);
lean_dec(v_traceState_242_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_281_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_261_; double v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_260_ = lean_box(0);
v___x_261_ = lean_box(0);
v___x_262_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0);
v___x_263_ = 0;
v___x_264_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_265_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_265_, 0, v_cls_227_);
lean_ctor_set(v___x_265_, 1, v___x_261_);
lean_ctor_set(v___x_265_, 2, v___x_264_);
lean_ctor_set_float(v___x_265_, sizeof(void*)*3, v___x_262_);
lean_ctor_set_float(v___x_265_, sizeof(void*)*3 + 8, v___x_262_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*3 + 16, v___x_263_);
v___x_266_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2));
v___x_267_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v_a_237_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
lean_inc(v_ref_235_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_ref_235_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Lean_PersistentArray_push___redArg(v_traces_256_, v___x_268_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_269_);
v___x_271_ = v___x_258_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_269_);
lean_ctor_set_uint64(v_reuseFailAlloc_280_, sizeof(void*)*1, v_tid_255_);
v___x_271_ = v_reuseFailAlloc_280_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_273_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 4, v___x_271_);
v___x_273_ = v___x_253_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_env_243_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_nextMacroScope_244_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_ngen_245_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_auxDeclNGen_246_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_cache_247_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_recordedDeps_248_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_messages_249_);
lean_ctor_set(v_reuseFailAlloc_279_, 8, v_infoState_250_);
lean_ctor_set(v_reuseFailAlloc_279_, 9, v_snapshotTasks_251_);
v___x_273_ = v_reuseFailAlloc_279_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_274_ = lean_st_ref_put(v___y_233_, v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_260_);
lean_ctor_set(v___x_275_, 1, v___y_229_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_275_);
v___x_277_ = v___x_239_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_227_ = stack[0].m_obj;
lean_object* v_msg_228_ = stack[1].m_obj;
lean_object* v___y_229_ = stack[2].m_obj;
lean_object* v___y_230_ = stack[3].m_obj;
lean_object* v___y_231_ = stack[4].m_obj;
lean_object* v___y_232_ = stack[5].m_obj;
lean_object* v___y_233_ = stack[6].m_obj;
lean_object* v_res_284_;
v_res_284_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_227_, v_msg_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
stack->m_obj
 = v_res_284_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_285_, lean_object* v_msg_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_285_, v_msg_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_293_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_keys_294_, lean_object* v_i_295_, lean_object* v_k_296_){
_start:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_array_get_size(v_keys_294_);
v___x_298_ = lean_nat_dec_lt(v_i_295_, v___x_297_);
if (v___x_298_ == 0)
{
lean_dec(v_i_295_);
return v___x_298_;
}
else
{
lean_object* v_k_x27_299_; uint8_t v___x_300_; 
v_k_x27_299_ = lean_array_fget_borrowed(v_keys_294_, v_i_295_);
v___x_300_ = l_Lean_instBEqExtraModUse_beq(v_k_296_, v_k_x27_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_i_295_, v___x_301_);
lean_dec(v_i_295_);
v_i_295_ = v___x_302_;
goto _start;
}
else
{
lean_dec(v_i_295_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_294_ = stack[0].m_obj;
lean_object* v_i_295_ = stack[1].m_obj;
lean_object* v_k_296_ = stack[2].m_obj;
uint8_t v_res_304_;
v_res_304_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_294_, v_i_295_, v_k_296_);
stack->m_num = v_res_304_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_keys_305_, lean_object* v_i_306_, lean_object* v_k_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_305_, v_i_306_, v_k_307_);
lean_dec_ref(v_k_307_);
lean_dec_ref(v_keys_305_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_310_, size_t v_x_311_, lean_object* v_x_312_){
_start:
{
if (lean_obj_tag(v_x_310_) == 0)
{
lean_object* v_es_313_; lean_object* v___x_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v_j_317_; lean_object* v___x_318_; 
v_es_313_ = lean_ctor_get(v_x_310_, 0);
v___x_314_ = lean_box(2);
v___x_315_ = ((size_t)31ULL);
v___x_316_ = lean_usize_land(v_x_311_, v___x_315_);
v_j_317_ = lean_usize_to_nat(v___x_316_);
v___x_318_ = lean_array_get_borrowed(v___x_314_, v_es_313_, v_j_317_);
lean_dec(v_j_317_);
switch(lean_obj_tag(v___x_318_))
{
case 0:
{
lean_object* v_key_319_; uint8_t v___x_320_; 
v_key_319_ = lean_ctor_get(v___x_318_, 0);
v___x_320_ = l_Lean_instBEqExtraModUse_beq(v_x_312_, v_key_319_);
return v___x_320_;
}
case 1:
{
lean_object* v_node_321_; size_t v___x_322_; size_t v___x_323_; 
v_node_321_ = lean_ctor_get(v___x_318_, 0);
v___x_322_ = ((size_t)5ULL);
v___x_323_ = lean_usize_shift_right(v_x_311_, v___x_322_);
v_x_310_ = v_node_321_;
v_x_311_ = v___x_323_;
goto _start;
}
default: 
{
uint8_t v___x_325_; 
v___x_325_ = 0;
return v___x_325_;
}
}
}
else
{
lean_object* v_ks_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_ks_326_ = lean_ctor_get(v_x_310_, 0);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_326_, v___x_327_, v_x_312_);
return v___x_328_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_310_ = stack[0].m_obj;
size_t v_x_311_ = stack[1].m_num;
lean_object* v_x_312_ = stack[2].m_obj;
uint8_t v_res_329_;
v_res_329_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_310_, v_x_311_, v_x_312_);
stack->m_num = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
size_t v_x_36454__boxed_333_; uint8_t v_res_334_; lean_object* v_r_335_; 
v_x_36454__boxed_333_ = lean_unbox_usize(v_x_331_);
lean_dec(v_x_331_);
v_res_334_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_330_, v_x_36454__boxed_333_, v_x_332_);
lean_dec_ref(v_x_332_);
lean_dec_ref(v_x_330_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
uint64_t v___x_338_; size_t v___x_339_; uint8_t v___x_340_; 
v___x_338_ = l_Lean_instHashableExtraModUse_hash(v_x_337_);
v___x_339_ = lean_uint64_to_usize(v___x_338_);
v___x_340_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_336_, v___x_339_, v_x_337_);
return v___x_340_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_336_ = stack[0].m_obj;
lean_object* v_x_337_ = stack[1].m_obj;
uint8_t v_res_341_;
v_res_341_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_336_, v_x_337_);
stack->m_num = v_res_341_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_342_, v_x_343_);
lean_dec_ref(v_x_343_);
lean_dec_ref(v_x_342_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_346_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1);
v___x_352_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
lean_ctor_set(v___x_352_, 3, v___x_351_);
lean_ctor_set(v___x_352_, 4, v___x_351_);
lean_ctor_set(v___x_352_, 5, v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_353_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v_cls_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_cls_368_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6));
v___x_369_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13));
v___x_370_ = l_Lean_Name_append(v___x_369_, v_cls_368_);
return v___x_370_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17));
v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
return v___x_376_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_381_, uint8_t v_isMeta_382_, lean_object* v_hint_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_env_426_; uint8_t v_isExporting_427_; lean_object* v_entry_428_; lean_object* v___x_429_; lean_object* v_env_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_424_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_425_ = lean_st_ref_get(v___y_388_);
v_env_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc_ref(v_env_426_);
lean_dec(v___x_425_);
v_isExporting_427_ = lean_ctor_get_uint8(v_env_426_, sizeof(void*)*13);
lean_dec_ref(v_env_426_);
lean_inc(v_mod_381_);
v_entry_428_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_428_, 0, v_mod_381_);
lean_ctor_set_uint8(v_entry_428_, sizeof(void*)*1, v_isExporting_427_);
lean_ctor_set_uint8(v_entry_428_, sizeof(void*)*1 + 1, v_isMeta_382_);
v___x_429_ = lean_st_ref_get(v___y_388_);
v_env_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_env_430_);
lean_dec(v___x_429_);
v___x_431_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_432_ = lean_box(1);
v___x_433_ = lean_box(0);
v___x_434_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_424_, v___x_431_, v_env_430_, v___x_432_, v___x_433_);
v___x_435_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_434_, v_entry_428_);
lean_dec(v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v_toCold_436_; lean_object* v_options_437_; lean_object* v_inheritedTraceOptions_438_; uint8_t v_hasTrace_439_; lean_object* v___f_440_; uint8_t v___x_441_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; 
v_toCold_436_ = lean_ctor_get(v___y_387_, 0);
v_options_437_ = lean_ctor_get(v_toCold_436_, 2);
v_inheritedTraceOptions_438_ = lean_ctor_get(v_toCold_436_, 11);
v_hasTrace_439_ = lean_ctor_get_uint8(v_options_437_, sizeof(void*)*1);
v___f_440_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_440_, 0, v___x_431_);
lean_closure_set(v___f_440_, 1, v_entry_428_);
v___x_441_ = 1;
if (v_hasTrace_439_ == 0)
{
lean_dec(v_hint_383_);
lean_dec(v_mod_381_);
v___y_443_ = v___y_384_;
v___y_444_ = v___y_386_;
v___y_445_ = v___y_388_;
goto v___jp_442_;
}
else
{
lean_object* v_cls_472_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_cls_472_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6));
v___x_494_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14);
v___x_495_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_438_, v_options_437_, v___x_494_);
if (v___x_495_ == 0)
{
lean_dec(v_hint_383_);
lean_dec(v_mod_381_);
v___y_443_ = v___y_384_;
v___y_444_ = v___y_386_;
v___y_445_ = v___y_388_;
goto v___jp_442_;
}
else
{
lean_object* v___x_496_; lean_object* v___y_498_; 
v___x_496_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
if (v_isExporting_427_ == 0)
{
lean_object* v___x_505_; 
v___x_505_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_498_ = v___x_505_;
goto v___jp_497_;
}
else
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
v___y_498_ = v___x_506_;
goto v___jp_497_;
}
v___jp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_inc_ref(v___y_498_);
v___x_499_ = l_Lean_stringToMessageData(v___y_498_);
v___x_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_496_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
v___x_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
if (v_isMeta_382_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___y_481_ = v___x_502_;
v___y_482_ = v___x_503_;
goto v___jp_480_;
}
else
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20));
v___y_481_ = v___x_502_;
v___y_482_ = v___x_504_;
goto v___jp_480_;
}
}
}
v___jp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___y_474_);
lean_ctor_set(v___x_476_, 1, v___y_475_);
v___x_477_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_472_, v___x_476_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v_snd_479_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
v_snd_479_ = lean_ctor_get(v_a_478_, 1);
lean_inc(v_snd_479_);
lean_dec(v_a_478_);
v___y_443_ = v_snd_479_;
v___y_444_ = v___y_386_;
v___y_445_ = v___y_388_;
goto v___jp_442_;
}
else
{
lean_dec_ref(v___f_440_);
return v___x_477_;
}
}
v___jp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
lean_inc_ref(v___y_482_);
v___x_483_ = l_Lean_stringToMessageData(v___y_482_);
v___x_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_484_, 0, v___y_481_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = l_Lean_MessageData_ofName(v_mod_381_);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_Name_isAnonymous(v_hint_383_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_491_ = l_Lean_MessageData_ofName(v_hint_383_);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___y_474_ = v___x_488_;
v___y_475_ = v___x_492_;
goto v___jp_473_;
}
else
{
lean_object* v___x_493_; 
lean_dec(v_hint_383_);
v___x_493_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11);
v___y_474_ = v___x_488_;
v___y_475_ = v___x_493_;
goto v___jp_473_;
}
}
}
v___jp_442_:
{
lean_object* v___x_446_; lean_object* v_toEnvExtension_447_; uint8_t v_logWrites_448_; 
v___x_446_ = lean_st_ref_take(v___y_445_);
v_toEnvExtension_447_ = lean_ctor_get(v___x_431_, 0);
v_logWrites_448_ = lean_ctor_get_uint8(v_toEnvExtension_447_, sizeof(void*)*6);
if (v_logWrites_448_ == 0)
{
lean_object* v_env_449_; lean_object* v_nextMacroScope_450_; lean_object* v_ngen_451_; lean_object* v_auxDeclNGen_452_; lean_object* v_traceState_453_; lean_object* v_recordedDeps_454_; lean_object* v_messages_455_; lean_object* v_infoState_456_; lean_object* v_snapshotTasks_457_; lean_object* v_asyncMode_458_; lean_object* v___x_459_; 
v_env_449_ = lean_ctor_get(v___x_446_, 0);
lean_inc_ref(v_env_449_);
v_nextMacroScope_450_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_nextMacroScope_450_);
v_ngen_451_ = lean_ctor_get(v___x_446_, 2);
lean_inc_ref(v_ngen_451_);
v_auxDeclNGen_452_ = lean_ctor_get(v___x_446_, 3);
lean_inc_ref(v_auxDeclNGen_452_);
v_traceState_453_ = lean_ctor_get(v___x_446_, 4);
lean_inc_ref(v_traceState_453_);
v_recordedDeps_454_ = lean_ctor_get(v___x_446_, 6);
lean_inc_ref(v_recordedDeps_454_);
v_messages_455_ = lean_ctor_get(v___x_446_, 7);
lean_inc_ref(v_messages_455_);
v_infoState_456_ = lean_ctor_get(v___x_446_, 8);
lean_inc_ref(v_infoState_456_);
v_snapshotTasks_457_ = lean_ctor_get(v___x_446_, 9);
lean_inc_ref(v_snapshotTasks_457_);
lean_dec(v___x_446_);
v_asyncMode_458_ = lean_ctor_get(v_toEnvExtension_447_, 2);
lean_inc_ref(v_toEnvExtension_447_);
v___x_459_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_447_, v_env_449_, v___f_440_, v_asyncMode_458_, v___x_433_, v___x_441_);
v___y_391_ = v___y_445_;
v___y_392_ = v_nextMacroScope_450_;
v___y_393_ = v_recordedDeps_454_;
v___y_394_ = v_traceState_453_;
v___y_395_ = v_auxDeclNGen_452_;
v___y_396_ = v_messages_455_;
v___y_397_ = v___y_443_;
v___y_398_ = v_infoState_456_;
v___y_399_ = v___y_444_;
v___y_400_ = v_snapshotTasks_457_;
v___y_401_ = v_ngen_451_;
v___y_402_ = v___x_459_;
goto v___jp_390_;
}
else
{
lean_object* v_env_460_; lean_object* v_nextMacroScope_461_; lean_object* v_ngen_462_; lean_object* v_auxDeclNGen_463_; lean_object* v_traceState_464_; lean_object* v_recordedDeps_465_; lean_object* v_messages_466_; lean_object* v_infoState_467_; lean_object* v_snapshotTasks_468_; lean_object* v_asyncMode_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_env_460_ = lean_ctor_get(v___x_446_, 0);
lean_inc_ref(v_env_460_);
v_nextMacroScope_461_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_nextMacroScope_461_);
v_ngen_462_ = lean_ctor_get(v___x_446_, 2);
lean_inc_ref(v_ngen_462_);
v_auxDeclNGen_463_ = lean_ctor_get(v___x_446_, 3);
lean_inc_ref(v_auxDeclNGen_463_);
v_traceState_464_ = lean_ctor_get(v___x_446_, 4);
lean_inc_ref(v_traceState_464_);
v_recordedDeps_465_ = lean_ctor_get(v___x_446_, 6);
lean_inc_ref(v_recordedDeps_465_);
v_messages_466_ = lean_ctor_get(v___x_446_, 7);
lean_inc_ref(v_messages_466_);
v_infoState_467_ = lean_ctor_get(v___x_446_, 8);
lean_inc_ref(v_infoState_467_);
v_snapshotTasks_468_ = lean_ctor_get(v___x_446_, 9);
lean_inc_ref(v_snapshotTasks_468_);
lean_dec(v___x_446_);
v_asyncMode_469_ = lean_ctor_get(v_toEnvExtension_447_, 2);
lean_inc_ref_n(v_toEnvExtension_447_, 2);
v___x_470_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_447_, v_env_460_);
lean_dec_ref(v_env_460_);
v___x_471_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_447_, v___x_470_, v___f_440_, v_asyncMode_469_, v___x_433_, v___x_441_);
v___y_391_ = v___y_445_;
v___y_392_ = v_nextMacroScope_461_;
v___y_393_ = v_recordedDeps_465_;
v___y_394_ = v_traceState_464_;
v___y_395_ = v_auxDeclNGen_463_;
v___y_396_ = v_messages_466_;
v___y_397_ = v___y_443_;
v___y_398_ = v_infoState_467_;
v___y_399_ = v___y_444_;
v___y_400_ = v_snapshotTasks_468_;
v___y_401_ = v_ngen_462_;
v___y_402_ = v___x_471_;
goto v___jp_390_;
}
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec_ref_known(v_entry_428_, 1);
lean_dec(v_hint_383_);
lean_dec(v_mod_381_);
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v___y_384_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
v___jp_390_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_mctx_407_; lean_object* v_zetaDeltaFVarIds_408_; lean_object* v_postponed_409_; lean_object* v_diag_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_422_; 
v___x_403_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
v___x_404_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_404_, 0, v___y_402_);
lean_ctor_set(v___x_404_, 1, v___y_392_);
lean_ctor_set(v___x_404_, 2, v___y_401_);
lean_ctor_set(v___x_404_, 3, v___y_395_);
lean_ctor_set(v___x_404_, 4, v___y_394_);
lean_ctor_set(v___x_404_, 5, v___x_403_);
lean_ctor_set(v___x_404_, 6, v___y_393_);
lean_ctor_set(v___x_404_, 7, v___y_396_);
lean_ctor_set(v___x_404_, 8, v___y_398_);
lean_ctor_set(v___x_404_, 9, v___y_400_);
v___x_405_ = lean_st_ref_put(v___y_391_, v___x_404_);
v___x_406_ = lean_st_ref_take(v___y_399_);
v_mctx_407_ = lean_ctor_get(v___x_406_, 0);
v_zetaDeltaFVarIds_408_ = lean_ctor_get(v___x_406_, 2);
v_postponed_409_ = lean_ctor_get(v___x_406_, 3);
v_diag_410_ = lean_ctor_get(v___x_406_, 4);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v___x_406_, 1);
lean_dec(v_unused_423_);
v___x_412_ = v___x_406_;
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_diag_410_);
lean_inc(v_postponed_409_);
lean_inc(v_zetaDeltaFVarIds_408_);
lean_inc(v_mctx_407_);
lean_dec(v___x_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_414_ = lean_box(0);
v___x_415_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_415_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_mctx_407_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_zetaDeltaFVarIds_408_);
lean_ctor_set(v_reuseFailAlloc_421_, 3, v_postponed_409_);
lean_ctor_set(v_reuseFailAlloc_421_, 4, v_diag_410_);
v___x_417_ = v_reuseFailAlloc_421_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_st_ref_put(v___y_399_, v___x_417_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_414_);
lean_ctor_set(v___x_419_, 1, v___y_397_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_381_ = stack[0].m_obj;
uint8_t v_isMeta_382_ = stack[1].m_num;
lean_object* v_hint_383_ = stack[2].m_obj;
lean_object* v___y_384_ = stack[3].m_obj;
lean_object* v___y_385_ = stack[4].m_obj;
lean_object* v___y_386_ = stack[5].m_obj;
lean_object* v___y_387_ = stack[6].m_obj;
lean_object* v___y_388_ = stack[7].m_obj;
lean_object* v_res_510_;
v_res_510_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_381_, v_isMeta_382_, v_hint_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
stack->m_obj
 = v_res_510_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object* v_a_522_, lean_object* v_x_523_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_531_, lean_object* v_x_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_531_, v_x_532_);
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
v___x_552_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_535_, v___x_551_);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_558_, lean_object* v_declName_559_, lean_object* v_as_560_, size_t v_sz_561_, size_t v_i_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_558_ = stack[0].m_obj;
lean_object* v_declName_559_ = stack[1].m_obj;
lean_object* v_as_560_ = stack[2].m_obj;
size_t v_sz_561_ = stack[3].m_num;
size_t v_i_562_ = stack[4].m_num;
lean_object* v_b_563_ = stack[5].m_obj;
lean_object* v___y_564_ = stack[6].m_obj;
lean_object* v___y_565_ = stack[7].m_obj;
lean_object* v___y_566_ = stack[8].m_obj;
lean_object* v___y_567_ = stack[9].m_obj;
lean_object* v___y_568_ = stack[10].m_obj;
lean_object* v_res_588_;
v_res_588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_558_, v_declName_559_, v_as_560_, v_sz_561_, v_i_562_, v_b_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_589_, lean_object* v_declName_590_, lean_object* v_as_591_, lean_object* v_sz_592_, lean_object* v_i_593_, lean_object* v_b_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
size_t v_sz_boxed_601_; size_t v_i_boxed_602_; lean_object* v_res_603_; 
v_sz_boxed_601_ = lean_unbox_usize(v_sz_592_);
lean_dec(v_sz_592_);
v_i_boxed_602_ = lean_unbox_usize(v_i_593_);
lean_dec(v_i_593_);
v_res_603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_589_, v_declName_590_, v_as_591_, v_sz_boxed_601_, v_i_boxed_602_, v_b_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v_as_591_);
lean_dec_ref(v___x_589_);
return v_res_603_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0(void){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_HashMap_instInhabited___redArg();
return v___x_604_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_607_, uint8_t v_isMeta_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_env_621_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___x_646_; 
v___x_615_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0);
v___x_616_ = lean_st_ref_get(v___y_613_);
v_env_621_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref(v_env_621_);
lean_dec(v___x_616_);
v___x_646_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_621_, v_declName_607_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_dec_ref(v_env_621_);
lean_dec(v_declName_607_);
goto v___jp_617_;
}
else
{
lean_object* v_val_647_; lean_object* v___x_648_; lean_object* v_modules_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_val_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = l_Lean_Environment_header(v_env_621_);
v_modules_649_ = lean_ctor_get(v___x_648_, 3);
lean_inc_ref(v_modules_649_);
lean_dec_ref(v___x_648_);
v___x_650_ = lean_array_get_size(v_modules_649_);
v___x_651_ = lean_nat_dec_lt(v_val_647_, v___x_650_);
if (v___x_651_ == 0)
{
lean_dec_ref(v_modules_649_);
lean_dec(v_val_647_);
lean_dec_ref(v_env_621_);
lean_dec(v_declName_607_);
goto v___jp_617_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___y_655_; 
v___x_652_ = lean_array_fget(v_modules_649_, v_val_647_);
lean_dec(v_val_647_);
lean_dec_ref(v_modules_649_);
v___x_653_ = lean_st_ref_get(v___y_613_);
if (v_isMeta_608_ == 0)
{
lean_dec(v___x_653_);
v___y_655_ = v_isMeta_608_;
goto v___jp_654_;
}
else
{
lean_object* v_env_668_; uint8_t v___x_669_; 
v_env_668_ = lean_ctor_get(v___x_653_, 0);
lean_inc_ref(v_env_668_);
lean_dec(v___x_653_);
lean_inc(v_declName_607_);
v___x_669_ = l_Lean_isMarkedMeta(v_env_668_, v_declName_607_);
if (v___x_669_ == 0)
{
v___y_655_ = v_isMeta_608_;
goto v___jp_654_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = 0;
v___y_655_ = v___x_670_;
goto v___jp_654_;
}
}
v___jp_654_:
{
lean_object* v_toImport_656_; lean_object* v_module_657_; lean_object* v___x_658_; 
v_toImport_656_ = lean_ctor_get(v___x_652_, 0);
lean_inc_ref(v_toImport_656_);
lean_dec(v___x_652_);
v_module_657_ = lean_ctor_get(v_toImport_656_, 0);
lean_inc(v_module_657_);
lean_dec_ref(v_toImport_656_);
lean_inc(v_declName_607_);
v___x_658_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_657_, v___y_655_, v_declName_607_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v_snd_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v_snd_660_ = lean_ctor_get(v_a_659_, 1);
lean_inc(v_snd_660_);
lean_dec(v_a_659_);
v___x_661_ = l_Lean_indirectModUseExt;
v___x_662_ = lean_box(1);
v___x_663_ = lean_box(0);
lean_inc_ref(v_env_621_);
v___x_664_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_615_, v___x_661_, v_env_621_, v___x_662_, v___x_663_);
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_664_, v_declName_607_);
lean_dec(v___x_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_666_; 
v___x_666_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___y_623_ = v_snd_660_;
v___y_624_ = v___x_666_;
goto v___jp_622_;
}
else
{
lean_object* v_val_667_; 
v_val_667_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v___x_665_, 1);
v___y_623_ = v_snd_660_;
v___y_624_ = v_val_667_;
goto v___jp_622_;
}
}
else
{
lean_dec_ref(v_env_621_);
lean_dec(v_declName_607_);
return v___x_658_;
}
}
}
}
v___jp_617_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = lean_box(0);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___y_609_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
v___jp_622_:
{
lean_object* v___x_625_; size_t v_sz_626_; size_t v___x_627_; lean_object* v___x_628_; 
v___x_625_ = lean_box(0);
v_sz_626_ = lean_array_size(v___y_624_);
v___x_627_ = ((size_t)0ULL);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_621_, v_declName_607_, v___y_624_, v_sz_626_, v___x_627_, v___x_625_, v___y_623_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec_ref(v___y_624_);
lean_dec_ref(v_env_621_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_645_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_645_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_645_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_645_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v_snd_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_643_; 
v_snd_633_ = lean_ctor_get(v_a_629_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_a_629_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v_a_629_, 0);
lean_dec(v_unused_644_);
v___x_635_ = v_a_629_;
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_snd_633_);
lean_dec(v_a_629_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_625_);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_snd_633_);
v___x_638_ = v_reuseFailAlloc_642_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_638_);
v___x_640_ = v___x_631_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
else
{
return v___x_628_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_607_ = stack[0].m_obj;
uint8_t v_isMeta_608_ = stack[1].m_num;
lean_object* v___y_609_ = stack[2].m_obj;
lean_object* v___y_610_ = stack[3].m_obj;
lean_object* v___y_611_ = stack[4].m_obj;
lean_object* v___y_612_ = stack[5].m_obj;
lean_object* v___y_613_ = stack[6].m_obj;
lean_object* v_res_671_;
v_res_671_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_607_, v_isMeta_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_672_, lean_object* v_isMeta_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
uint8_t v_isMeta_boxed_680_; lean_object* v_res_681_; 
v_isMeta_boxed_680_ = lean_unbox(v_isMeta_673_);
v_res_681_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_672_, v_isMeta_boxed_680_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v_res_681_;
}
}
lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___y_697_; lean_object* v_f_701_; uint8_t v___x_702_; 
v_f_701_ = l_Lean_Expr_getAppFn(v_e_689_);
v___x_702_ = l_Lean_Expr_isConst(v_f_701_);
if (v___x_702_ == 0)
{
lean_dec_ref(v_f_701_);
lean_dec_ref(v_e_689_);
v___y_697_ = v___y_690_;
goto v___jp_696_;
}
else
{
lean_object* v_declName_703_; lean_object* v___x_704_; lean_object* v_env_705_; uint8_t v___x_706_; 
v_declName_703_ = l_Lean_Expr_constName_x21(v_f_701_);
lean_dec_ref(v_f_701_);
v___x_704_ = lean_st_ref_get(v___y_694_);
v_env_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc_ref(v_env_705_);
lean_dec(v___x_704_);
lean_inc(v_declName_703_);
v___x_706_ = l_Lean_Meta_isCoeDecl(v_env_705_, v_declName_703_);
if (v___x_706_ == 0)
{
lean_dec(v_declName_703_);
lean_dec_ref(v_e_689_);
v___y_697_ = v___y_690_;
goto v___jp_696_;
}
else
{
lean_object* v___x_707_; 
lean_inc(v_declName_703_);
lean_inc_ref(v_e_689_);
v___x_707_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_689_, v_declName_703_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; uint8_t v___x_709_; lean_object* v___x_710_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = 0;
v___x_710_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_708_, v___x_709_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v_snd_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_763_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v_snd_712_ = lean_ctor_get(v_a_711_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_a_711_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v_a_711_, 0);
lean_dec(v_unused_764_);
v___x_714_ = v_a_711_;
v_isShared_715_ = v_isSharedCheck_763_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_snd_712_);
lean_dec(v_a_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_763_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; 
lean_inc_ref(v_e_689_);
v___x_716_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_689_, v___x_709_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_754_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_754_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_754_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_754_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
if (lean_obj_tag(v_a_717_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_753_; 
v_val_721_ = lean_ctor_get(v_a_717_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v_a_717_);
if (v_isSharedCheck_753_ == 0)
{
v___x_723_ = v_a_717_;
v_isShared_724_ = v_isSharedCheck_753_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_val_721_);
lean_dec(v_a_717_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_753_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___y_726_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_738_ = lean_name_eq(v_declName_703_, v___x_737_);
lean_dec(v_declName_703_);
if (v___x_738_ == 0)
{
lean_dec_ref(v_e_689_);
v___y_726_ = v_snd_712_;
goto v___jp_725_;
}
else
{
lean_object* v_dummy_739_; lean_object* v_nargs_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_dummy_739_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_740_ = l_Lean_Expr_getAppNumArgs(v_e_689_);
lean_inc(v_nargs_740_);
v___x_741_ = lean_mk_array(v_nargs_740_, v_dummy_739_);
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_sub(v_nargs_740_, v___x_742_);
lean_dec(v_nargs_740_);
v___x_744_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_689_, v___x_741_, v___x_743_);
v___x_745_ = lean_unsigned_to_nat(2u);
v___x_746_ = lean_array_get_size(v___x_744_);
v___x_747_ = lean_nat_dec_lt(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_dec_ref(v___x_744_);
v___y_726_ = v_snd_712_;
goto v___jp_725_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = lean_array_fget(v___x_744_, v___x_745_);
lean_dec_ref(v___x_744_);
v___x_749_ = l_Lean_Expr_getAppFn(v___x_748_);
lean_dec(v___x_748_);
v___x_750_ = l_Lean_Expr_isConst(v___x_749_);
if (v___x_750_ == 0)
{
lean_dec_ref(v___x_749_);
v___y_726_ = v_snd_712_;
goto v___jp_725_;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = l_Lean_Expr_constName_x21(v___x_749_);
lean_dec_ref(v___x_749_);
v___x_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v_snd_712_);
v___y_726_ = v___x_752_;
goto v___jp_725_;
}
}
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = l_Lean_Expr_headBeta(v_val_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_727_);
v___x_729_ = v___x_723_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_736_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v___y_726_);
lean_ctor_set(v___x_714_, 0, v___x_729_);
v___x_731_ = v___x_714_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___y_726_);
v___x_731_ = v_reuseFailAlloc_735_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_731_);
v___x_733_ = v___x_719_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_719_);
lean_dec(v_a_717_);
lean_del_object(v___x_714_);
lean_dec(v_declName_703_);
lean_dec_ref(v_e_689_);
v___y_697_ = v_snd_712_;
goto v___jp_696_;
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_del_object(v___x_714_);
lean_dec(v_snd_712_);
lean_dec(v_declName_703_);
lean_dec_ref(v_e_689_);
v_a_755_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_716_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_716_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_declName_703_);
lean_dec_ref(v_e_689_);
v_a_765_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_710_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_710_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_declName_703_);
lean_dec(v___y_690_);
lean_dec_ref(v_e_689_);
v_a_773_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_707_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_707_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
v___jp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___y_697_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_expandCoe___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_689_ = stack[0].m_obj;
lean_object* v___y_690_ = stack[1].m_obj;
lean_object* v___y_691_ = stack[2].m_obj;
lean_object* v___y_692_ = stack[3].m_obj;
lean_object* v___y_693_ = stack[4].m_obj;
lean_object* v___y_694_ = stack[5].m_obj;
lean_object* v_res_781_;
v_res_781_ = l_Lean_Meta_expandCoe___lam__1(v_e_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
stack->m_obj
 = v_res_781_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Meta_expandCoe___lam__1(v_e_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_789_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(lean_object* v_k_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v_b_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
lean_inc(v___y_795_);
lean_inc_ref(v___y_794_);
lean_inc(v___y_791_);
v___x_799_ = lean_apply_8(v_k_790_, v_b_793_, v___y_791_, v___y_792_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, lean_box(0));
return v___x_799_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_790_ = stack[0].m_obj;
lean_object* v___y_791_ = stack[1].m_obj;
lean_object* v___y_792_ = stack[2].m_obj;
lean_object* v_b_793_ = stack[3].m_obj;
lean_object* v___y_794_ = stack[4].m_obj;
lean_object* v___y_795_ = stack[5].m_obj;
lean_object* v___y_796_ = stack[6].m_obj;
lean_object* v___y_797_ = stack[7].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(v_k_790_, v___y_791_, v___y_792_, v_b_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed(lean_object* v_k_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v_b_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(v_k_801_, v___y_802_, v___y_803_, v_b_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_802_);
return v_res_810_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object* v_name_811_, uint8_t v_bi_812_, lean_object* v_type_813_, lean_object* v_k_814_, uint8_t v_kind_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___f_823_; lean_object* v___x_824_; 
lean_inc(v___y_816_);
v___f_823_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_823_, 0, v_k_814_);
lean_closure_set(v___f_823_, 1, v___y_816_);
lean_closure_set(v___f_823_, 2, v___y_817_);
v___x_824_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_811_, v_bi_812_, v_type_813_, v___f_823_, v_kind_815_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_a_833_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_824_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_824_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_811_ = stack[0].m_obj;
uint8_t v_bi_812_ = stack[1].m_num;
lean_object* v_type_813_ = stack[2].m_obj;
lean_object* v_k_814_ = stack[3].m_obj;
uint8_t v_kind_815_ = stack[4].m_num;
lean_object* v___y_816_ = stack[5].m_obj;
lean_object* v___y_817_ = stack[6].m_obj;
lean_object* v___y_818_ = stack[7].m_obj;
lean_object* v___y_819_ = stack[8].m_obj;
lean_object* v___y_820_ = stack[9].m_obj;
lean_object* v___y_821_ = stack[10].m_obj;
lean_object* v_res_841_;
v_res_841_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_811_, v_bi_812_, v_type_813_, v_k_814_, v_kind_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
stack->m_obj
 = v_res_841_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object* v_name_842_, lean_object* v_bi_843_, lean_object* v_type_844_, lean_object* v_k_845_, lean_object* v_kind_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
uint8_t v_bi_boxed_854_; uint8_t v_kind_boxed_855_; lean_object* v_res_856_; 
v_bi_boxed_854_ = lean_unbox(v_bi_843_);
v_kind_boxed_855_ = lean_unbox(v_kind_846_);
v_res_856_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_842_, v_bi_boxed_854_, v_type_844_, v_k_845_, v_kind_boxed_855_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_847_);
return v_res_856_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object* v___x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_857_);
lean_ctor_set(v___x_864_, 1, v___y_858_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_857_ = stack[0].m_obj;
lean_object* v___y_858_ = stack[1].m_obj;
lean_object* v___y_859_ = stack[2].m_obj;
lean_object* v___y_860_ = stack[3].m_obj;
lean_object* v___y_861_ = stack[4].m_obj;
lean_object* v___y_862_ = stack[5].m_obj;
lean_object* v_res_866_;
v_res_866_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_874_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(lean_object* v_name_875_, lean_object* v_type_876_, lean_object* v_val_877_, lean_object* v_k_878_, uint8_t v_nondep_879_, uint8_t v_kind_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___f_888_; lean_object* v___x_889_; 
lean_inc(v___y_881_);
v___f_888_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_888_, 0, v_k_878_);
lean_closure_set(v___f_888_, 1, v___y_881_);
lean_closure_set(v___f_888_, 2, v___y_882_);
v___x_889_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_875_, v_type_876_, v_val_877_, v___f_888_, v_nondep_879_, v_kind_880_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
v_a_898_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_889_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_889_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_875_ = stack[0].m_obj;
lean_object* v_type_876_ = stack[1].m_obj;
lean_object* v_val_877_ = stack[2].m_obj;
lean_object* v_k_878_ = stack[3].m_obj;
uint8_t v_nondep_879_ = stack[4].m_num;
uint8_t v_kind_880_ = stack[5].m_num;
lean_object* v___y_881_ = stack[6].m_obj;
lean_object* v___y_882_ = stack[7].m_obj;
lean_object* v___y_883_ = stack[8].m_obj;
lean_object* v___y_884_ = stack[9].m_obj;
lean_object* v___y_885_ = stack[10].m_obj;
lean_object* v___y_886_ = stack[11].m_obj;
lean_object* v_res_906_;
v_res_906_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_875_, v_type_876_, v_val_877_, v_k_878_, v_nondep_879_, v_kind_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg___boxed(lean_object* v_name_907_, lean_object* v_type_908_, lean_object* v_val_909_, lean_object* v_k_910_, lean_object* v_nondep_911_, lean_object* v_kind_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v_nondep_boxed_920_; uint8_t v_kind_boxed_921_; lean_object* v_res_922_; 
v_nondep_boxed_920_ = lean_unbox(v_nondep_911_);
v_kind_boxed_921_ = lean_unbox(v_kind_912_);
v_res_922_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_907_, v_type_908_, v_val_909_, v_k_910_, v_nondep_boxed_920_, v_kind_boxed_921_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_913_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(lean_object* v_a_923_, lean_object* v_b_924_, lean_object* v_x_925_){
_start:
{
if (lean_obj_tag(v_x_925_) == 0)
{
lean_dec(v_b_924_);
lean_dec_ref(v_a_923_);
return v_x_925_;
}
else
{
lean_object* v_key_926_; lean_object* v_value_927_; lean_object* v_tail_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_940_; 
v_key_926_ = lean_ctor_get(v_x_925_, 0);
v_value_927_ = lean_ctor_get(v_x_925_, 1);
v_tail_928_ = lean_ctor_get(v_x_925_, 2);
v_isSharedCheck_940_ = !lean_is_exclusive(v_x_925_);
if (v_isSharedCheck_940_ == 0)
{
v___x_930_ = v_x_925_;
v_isShared_931_ = v_isSharedCheck_940_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_tail_928_);
lean_inc(v_value_927_);
lean_inc(v_key_926_);
lean_dec(v_x_925_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_940_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
uint8_t v___x_932_; 
v___x_932_ = l_Lean_ExprStructEq_beq(v_key_926_, v_a_923_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_923_, v_b_924_, v_tail_928_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 2, v___x_933_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_key_926_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_value_927_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
else
{
lean_object* v___x_938_; 
lean_dec(v_value_927_);
lean_dec(v_key_926_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v_b_924_);
lean_ctor_set(v___x_930_, 0, v_a_923_);
v___x_938_ = v___x_930_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_923_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_b_924_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_tail_928_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object* v_a_941_, lean_object* v_x_942_){
_start:
{
if (lean_obj_tag(v_x_942_) == 0)
{
uint8_t v___x_943_; 
v___x_943_ = 0;
return v___x_943_;
}
else
{
lean_object* v_key_944_; lean_object* v_tail_945_; uint8_t v___x_946_; 
v_key_944_ = lean_ctor_get(v_x_942_, 0);
v_tail_945_ = lean_ctor_get(v_x_942_, 2);
v___x_946_ = l_Lean_ExprStructEq_beq(v_key_944_, v_a_941_);
if (v___x_946_ == 0)
{
v_x_942_ = v_tail_945_;
goto _start;
}
else
{
return v___x_946_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_941_ = stack[0].m_obj;
lean_object* v_x_942_ = stack[1].m_obj;
uint8_t v_res_948_;
v_res_948_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_941_, v_x_942_);
stack->m_num = v_res_948_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object* v_a_949_, lean_object* v_x_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_949_, v_x_950_);
lean_dec(v_x_950_);
lean_dec_ref(v_a_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
return v_x_953_;
}
else
{
lean_object* v_key_955_; lean_object* v_value_956_; lean_object* v_tail_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_980_; 
v_key_955_ = lean_ctor_get(v_x_954_, 0);
v_value_956_ = lean_ctor_get(v_x_954_, 1);
v_tail_957_ = lean_ctor_get(v_x_954_, 2);
v_isSharedCheck_980_ = !lean_is_exclusive(v_x_954_);
if (v_isSharedCheck_980_ == 0)
{
v___x_959_ = v_x_954_;
v_isShared_960_ = v_isSharedCheck_980_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_tail_957_);
lean_inc(v_value_956_);
lean_inc(v_key_955_);
lean_dec(v_x_954_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_980_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; uint64_t v___x_962_; uint64_t v___x_963_; uint64_t v___x_964_; uint64_t v_fold_965_; uint64_t v___x_966_; uint64_t v___x_967_; uint64_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_961_ = lean_array_get_size(v_x_953_);
v___x_962_ = l_Lean_ExprStructEq_hash(v_key_955_);
v___x_963_ = 32ULL;
v___x_964_ = lean_uint64_shift_right(v___x_962_, v___x_963_);
v_fold_965_ = lean_uint64_xor(v___x_962_, v___x_964_);
v___x_966_ = 16ULL;
v___x_967_ = lean_uint64_shift_right(v_fold_965_, v___x_966_);
v___x_968_ = lean_uint64_xor(v_fold_965_, v___x_967_);
v___x_969_ = lean_uint64_to_usize(v___x_968_);
v___x_970_ = lean_usize_of_nat(v___x_961_);
v___x_971_ = ((size_t)1ULL);
v___x_972_ = lean_usize_sub(v___x_970_, v___x_971_);
v___x_973_ = lean_usize_land(v___x_969_, v___x_972_);
v___x_974_ = lean_array_uget_borrowed(v_x_953_, v___x_973_);
lean_inc(v___x_974_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 2, v___x_974_);
v___x_976_ = v___x_959_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_key_955_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_value_956_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v___x_974_);
v___x_976_ = v_reuseFailAlloc_979_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; 
v___x_977_ = lean_array_uset(v_x_953_, v___x_973_, v___x_976_);
v_x_953_ = v___x_977_;
v_x_954_ = v_tail_957_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(lean_object* v_i_981_, lean_object* v_source_982_, lean_object* v_target_983_){
_start:
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = lean_array_get_size(v_source_982_);
v___x_985_ = lean_nat_dec_lt(v_i_981_, v___x_984_);
if (v___x_985_ == 0)
{
lean_dec_ref(v_source_982_);
lean_dec(v_i_981_);
return v_target_983_;
}
else
{
lean_object* v_es_986_; lean_object* v___x_987_; lean_object* v_source_988_; lean_object* v_target_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_es_986_ = lean_array_fget(v_source_982_, v_i_981_);
v___x_987_ = lean_box(0);
v_source_988_ = lean_array_fset(v_source_982_, v_i_981_, v___x_987_);
v_target_989_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_target_983_, v_es_986_);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_add(v_i_981_, v___x_990_);
lean_dec(v_i_981_);
v_i_981_ = v___x_991_;
v_source_982_ = v_source_988_;
v_target_983_ = v_target_989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object* v_data_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_nbuckets_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_994_ = lean_array_get_size(v_data_993_);
v___x_995_ = lean_unsigned_to_nat(2u);
v_nbuckets_996_ = lean_nat_mul(v___x_994_, v___x_995_);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_box(0);
v___x_999_ = lean_mk_array(v_nbuckets_996_, v___x_998_);
v___x_1000_ = lean_array_propagate_mark(v_data_993_, v___x_999_);
v___x_1001_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v___x_997_, v_data_993_, v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_m_1002_, lean_object* v_a_1003_, lean_object* v_b_1004_){
_start:
{
lean_object* v_size_1005_; lean_object* v_buckets_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1049_; 
v_size_1005_ = lean_ctor_get(v_m_1002_, 0);
v_buckets_1006_ = lean_ctor_get(v_m_1002_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_m_1002_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1008_ = v_m_1002_;
v_isShared_1009_ = v_isSharedCheck_1049_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_buckets_1006_);
lean_inc(v_size_1005_);
lean_dec(v_m_1002_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1049_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; uint64_t v___x_1011_; uint64_t v___x_1012_; uint64_t v___x_1013_; uint64_t v_fold_1014_; uint64_t v___x_1015_; uint64_t v___x_1016_; uint64_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; size_t v___x_1022_; lean_object* v_bkt_1023_; uint8_t v___x_1024_; 
v___x_1010_ = lean_array_get_size(v_buckets_1006_);
v___x_1011_ = l_Lean_ExprStructEq_hash(v_a_1003_);
v___x_1012_ = 32ULL;
v___x_1013_ = lean_uint64_shift_right(v___x_1011_, v___x_1012_);
v_fold_1014_ = lean_uint64_xor(v___x_1011_, v___x_1013_);
v___x_1015_ = 16ULL;
v___x_1016_ = lean_uint64_shift_right(v_fold_1014_, v___x_1015_);
v___x_1017_ = lean_uint64_xor(v_fold_1014_, v___x_1016_);
v___x_1018_ = lean_uint64_to_usize(v___x_1017_);
v___x_1019_ = lean_usize_of_nat(v___x_1010_);
v___x_1020_ = ((size_t)1ULL);
v___x_1021_ = lean_usize_sub(v___x_1019_, v___x_1020_);
v___x_1022_ = lean_usize_land(v___x_1018_, v___x_1021_);
v_bkt_1023_ = lean_array_uget_borrowed(v_buckets_1006_, v___x_1022_);
v___x_1024_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_1003_, v_bkt_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v_size_x27_1026_; lean_object* v___x_1027_; lean_object* v_buckets_x27_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1025_ = lean_unsigned_to_nat(1u);
v_size_x27_1026_ = lean_nat_add(v_size_1005_, v___x_1025_);
lean_dec(v_size_1005_);
lean_inc(v_bkt_1023_);
v___x_1027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1027_, 0, v_a_1003_);
lean_ctor_set(v___x_1027_, 1, v_b_1004_);
lean_ctor_set(v___x_1027_, 2, v_bkt_1023_);
v_buckets_x27_1028_ = lean_array_uset(v_buckets_1006_, v___x_1022_, v___x_1027_);
v___x_1029_ = lean_unsigned_to_nat(4u);
v___x_1030_ = lean_nat_mul(v_size_x27_1026_, v___x_1029_);
v___x_1031_ = lean_unsigned_to_nat(3u);
v___x_1032_ = lean_nat_div(v___x_1030_, v___x_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_array_get_size(v_buckets_x27_1028_);
v___x_1034_ = lean_nat_dec_le(v___x_1032_, v___x_1033_);
lean_dec(v___x_1032_);
if (v___x_1034_ == 0)
{
lean_object* v_val_1035_; lean_object* v___x_1037_; 
v_val_1035_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_buckets_x27_1028_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_val_1035_);
lean_ctor_set(v___x_1008_, 0, v_size_x27_1026_);
v___x_1037_ = v___x_1008_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_size_x27_1026_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_val_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
else
{
lean_object* v___x_1040_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_buckets_x27_1028_);
lean_ctor_set(v___x_1008_, 0, v_size_x27_1026_);
v___x_1040_ = v___x_1008_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_size_x27_1026_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_buckets_x27_1028_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
else
{
lean_object* v___x_1042_; lean_object* v_buckets_x27_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
lean_inc(v_bkt_1023_);
v___x_1042_ = lean_box(0);
v_buckets_x27_1043_ = lean_array_uset(v_buckets_1006_, v___x_1022_, v___x_1042_);
v___x_1044_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_1003_, v_b_1004_, v_bkt_1023_);
v___x_1045_ = lean_array_uset(v_buckets_x27_1043_, v___x_1022_, v___x_1044_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___x_1045_);
v___x_1047_ = v___x_1008_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_size_1005_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_1050_, lean_object* v_e_1051_, lean_object* v_fst_1052_){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1054_ = lean_st_ref_take(v_a_1050_);
v___x_1055_ = lean_box(0);
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_1054_, v_e_1051_, v_fst_1052_);
v___x_1057_ = lean_st_ref_put(v_a_1050_, v___x_1056_);
return v___x_1055_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1050_ = stack[0].m_obj;
lean_object* v_e_1051_ = stack[1].m_obj;
lean_object* v_fst_1052_ = stack[2].m_obj;
lean_object* v_res_1058_;
v_res_1058_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1050_, v_e_1051_, v_fst_1052_);
stack->m_obj
 = v_res_1058_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_1059_, lean_object* v_e_1060_, lean_object* v_fst_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1059_, v_e_1060_, v_fst_1061_);
lean_dec(v_a_1059_);
return v_res_1063_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = l_Lean_maxRecDepthErrorMessage;
v___x_1070_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3);
v___x_1072_ = l_Lean_MessageData_ofFormat(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4);
v___x_1074_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2));
v___x_1075_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1073_);
return v___x_1075_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(lean_object* v_ref_1076_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_ref_1076_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1076_ = stack[0].m_obj;
lean_object* v_res_1081_;
v_res_1081_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1076_);
stack->m_obj
 = v_res_1081_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___boxed(lean_object* v_ref_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1082_);
return v_res_1084_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object* v_x_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___y_1094_; lean_object* v_toCold_1111_; lean_object* v_currRecDepth_1112_; lean_object* v_ref_1113_; uint16_t v_optionFlags_1114_; uint8_t v_suppressElabErrors_1115_; uint8_t v_isRecordingDeps_1116_; lean_object* v_maxRecDepth_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_toCold_1111_ = lean_ctor_get(v___y_1090_, 0);
v_currRecDepth_1112_ = lean_ctor_get(v___y_1090_, 1);
v_ref_1113_ = lean_ctor_get(v___y_1090_, 2);
v_optionFlags_1114_ = lean_ctor_get_uint16(v___y_1090_, sizeof(void*)*3);
v_suppressElabErrors_1115_ = lean_ctor_get_uint8(v___y_1090_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1116_ = lean_ctor_get_uint8(v___y_1090_, sizeof(void*)*3 + 3);
v_maxRecDepth_1122_ = lean_ctor_get(v_toCold_1111_, 3);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_nat_dec_eq(v_maxRecDepth_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_nat_dec_eq(v_currRecDepth_1112_, v_maxRecDepth_1122_);
if (v___x_1125_ == 0)
{
goto v___jp_1117_;
}
else
{
lean_object* v___x_1126_; 
lean_dec(v___y_1087_);
lean_dec_ref(v_x_1085_);
lean_inc(v_ref_1113_);
v___x_1126_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1113_);
v___y_1094_ = v___x_1126_;
goto v___jp_1093_;
}
}
else
{
goto v___jp_1117_;
}
v___jp_1093_:
{
if (lean_obj_tag(v___y_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___y_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___y_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___y_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___y_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___y_1094_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___y_1094_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___y_1094_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___y_1094_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
v___jp_1117_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_add(v_currRecDepth_1112_, v___x_1118_);
lean_inc(v_ref_1113_);
lean_inc_ref(v_toCold_1111_);
v___x_1120_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1120_, 0, v_toCold_1111_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
lean_ctor_set(v___x_1120_, 2, v_ref_1113_);
lean_ctor_set_uint16(v___x_1120_, sizeof(void*)*3, v_optionFlags_1114_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*3 + 2, v_suppressElabErrors_1115_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*3 + 3, v_isRecordingDeps_1116_);
lean_inc(v___y_1091_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1088_);
lean_inc(v___y_1086_);
v___x_1121_ = lean_apply_7(v_x_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___x_1120_, v___y_1091_, lean_box(0));
v___y_1094_ = v___x_1121_;
goto v___jp_1093_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1085_ = stack[0].m_obj;
lean_object* v___y_1086_ = stack[1].m_obj;
lean_object* v___y_1087_ = stack[2].m_obj;
lean_object* v___y_1088_ = stack[3].m_obj;
lean_object* v___y_1089_ = stack[4].m_obj;
lean_object* v___y_1090_ = stack[5].m_obj;
lean_object* v___y_1091_ = stack[6].m_obj;
lean_object* v_res_1127_;
v_res_1127_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
stack->m_obj
 = v_res_1127_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1129_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(lean_object* v_a_1137_, lean_object* v_x_1138_){
_start:
{
if (lean_obj_tag(v_x_1138_) == 0)
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_box(0);
return v___x_1139_;
}
else
{
lean_object* v_key_1140_; lean_object* v_value_1141_; lean_object* v_tail_1142_; uint8_t v___x_1143_; 
v_key_1140_ = lean_ctor_get(v_x_1138_, 0);
v_value_1141_ = lean_ctor_get(v_x_1138_, 1);
v_tail_1142_ = lean_ctor_get(v_x_1138_, 2);
v___x_1143_ = l_Lean_ExprStructEq_beq(v_key_1140_, v_a_1137_);
if (v___x_1143_ == 0)
{
v_x_1138_ = v_tail_1142_;
goto _start;
}
else
{
lean_object* v___x_1145_; 
lean_inc(v_value_1141_);
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_value_1141_);
return v___x_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(lean_object* v_a_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1146_, v_x_1147_);
lean_dec(v_x_1147_);
lean_dec_ref(v_a_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_m_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_buckets_1151_; lean_object* v___x_1152_; uint64_t v___x_1153_; uint64_t v___x_1154_; uint64_t v___x_1155_; uint64_t v_fold_1156_; uint64_t v___x_1157_; uint64_t v___x_1158_; uint64_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_buckets_1151_ = lean_ctor_get(v_m_1149_, 1);
v___x_1152_ = lean_array_get_size(v_buckets_1151_);
v___x_1153_ = l_Lean_ExprStructEq_hash(v_a_1150_);
v___x_1154_ = 32ULL;
v___x_1155_ = lean_uint64_shift_right(v___x_1153_, v___x_1154_);
v_fold_1156_ = lean_uint64_xor(v___x_1153_, v___x_1155_);
v___x_1157_ = 16ULL;
v___x_1158_ = lean_uint64_shift_right(v_fold_1156_, v___x_1157_);
v___x_1159_ = lean_uint64_xor(v_fold_1156_, v___x_1158_);
v___x_1160_ = lean_uint64_to_usize(v___x_1159_);
v___x_1161_ = lean_usize_of_nat(v___x_1152_);
v___x_1162_ = ((size_t)1ULL);
v___x_1163_ = lean_usize_sub(v___x_1161_, v___x_1162_);
v___x_1164_ = lean_usize_land(v___x_1160_, v___x_1163_);
v___x_1165_ = lean_array_uget_borrowed(v_buckets_1151_, v___x_1164_);
v___x_1166_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1150_, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_m_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_1167_, v_a_1168_);
lean_dec_ref(v_a_1168_);
lean_dec_ref(v_m_1167_);
return v_res_1169_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1170_, lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_apply_1(v_x_1171_, lean_box(0));
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v___y_1172_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1171_ = stack[1].m_obj;
lean_object* v___y_1172_ = stack[2].m_obj;
lean_object* v___y_1173_ = stack[3].m_obj;
lean_object* v___y_1174_ = stack[4].m_obj;
lean_object* v___y_1175_ = stack[5].m_obj;
lean_object* v___y_1176_ = stack[6].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v_x_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_x_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1182_, v_x_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1191_, lean_object* v_pre_1192_, lean_object* v_post_1193_, lean_object* v_usedLetOnly_1194_, lean_object* v_skipConstInApp_1195_, lean_object* v_skipInstances_1196_, lean_object* v_body_1197_, lean_object* v_x_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v_usedLetOnly_boxed_1206_; uint8_t v_skipConstInApp_boxed_1207_; uint8_t v_skipInstances_boxed_1208_; lean_object* v_res_1209_; 
v_usedLetOnly_boxed_1206_ = lean_unbox(v_usedLetOnly_1194_);
v_skipConstInApp_boxed_1207_ = lean_unbox(v_skipConstInApp_1195_);
v_skipInstances_boxed_1208_ = lean_unbox(v_skipInstances_1196_);
v_res_1209_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1191_, v_pre_1192_, v_post_1193_, v_usedLetOnly_boxed_1206_, v_skipConstInApp_boxed_1207_, v_skipInstances_boxed_1208_, v_body_1197_, v_x_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1199_);
return v_res_1209_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1213_, lean_object* v_pre_1214_, lean_object* v_post_1215_, uint8_t v_usedLetOnly_1216_, uint8_t v_skipConstInApp_1217_, uint8_t v_skipInstances_1218_, lean_object* v_body_1219_, lean_object* v_x_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_array_push(v_fvars_1213_, v_x_1220_);
v___x_1229_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1214_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v___x_1228_, v_body_1219_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1229_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1213_ = stack[0].m_obj;
lean_object* v_pre_1214_ = stack[1].m_obj;
lean_object* v_post_1215_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1216_ = stack[3].m_num;
uint8_t v_skipConstInApp_1217_ = stack[4].m_num;
uint8_t v_skipInstances_1218_ = stack[5].m_num;
lean_object* v_body_1219_ = stack[6].m_obj;
lean_object* v_x_1220_ = stack[7].m_obj;
lean_object* v___y_1221_ = stack[8].m_obj;
lean_object* v___y_1222_ = stack[9].m_obj;
lean_object* v___y_1223_ = stack[10].m_obj;
lean_object* v___y_1224_ = stack[11].m_obj;
lean_object* v___y_1225_ = stack[12].m_obj;
lean_object* v___y_1226_ = stack[13].m_obj;
lean_object* v_res_1230_;
v_res_1230_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1213_, v_pre_1214_, v_post_1215_, v_usedLetOnly_1216_, v_skipConstInApp_1217_, v_skipInstances_1218_, v_body_1219_, v_x_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
stack->m_obj
 = v_res_1230_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1231_, lean_object* v_pre_1232_, lean_object* v_post_1233_, lean_object* v_usedLetOnly_1234_, lean_object* v_skipConstInApp_1235_, lean_object* v_skipInstances_1236_, lean_object* v_body_1237_, lean_object* v_x_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v_usedLetOnly_boxed_1246_; uint8_t v_skipConstInApp_boxed_1247_; uint8_t v_skipInstances_boxed_1248_; lean_object* v_res_1249_; 
v_usedLetOnly_boxed_1246_ = lean_unbox(v_usedLetOnly_1234_);
v_skipConstInApp_boxed_1247_ = lean_unbox(v_skipConstInApp_1235_);
v_skipInstances_boxed_1248_ = lean_unbox(v_skipInstances_1236_);
v_res_1249_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1231_, v_pre_1232_, v_post_1233_, v_usedLetOnly_boxed_1246_, v_skipConstInApp_boxed_1247_, v_skipInstances_boxed_1248_, v_body_1237_, v_x_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1239_);
return v_res_1249_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1250_, lean_object* v_post_1251_, uint8_t v_usedLetOnly_1252_, uint8_t v_skipConstInApp_1253_, uint8_t v_skipInstances_1254_, lean_object* v_e_1255_, lean_object* v_a_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; 
lean_inc_ref(v_post_1251_);
lean_inc(v___y_1261_);
lean_inc_ref(v___y_1260_);
lean_inc(v___y_1259_);
lean_inc_ref(v___y_1258_);
lean_inc_ref(v_e_1255_);
v___x_1263_ = lean_apply_7(v_post_1251_, v_e_1255_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, lean_box(0));
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1295_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1295_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1295_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_fst_1268_; lean_object* v_snd_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1294_; 
v_fst_1268_ = lean_ctor_get(v_a_1264_, 0);
v_snd_1269_ = lean_ctor_get(v_a_1264_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_a_1264_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1271_ = v_a_1264_;
v_isShared_1272_ = v_isSharedCheck_1294_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_snd_1269_);
lean_inc(v_fst_1268_);
lean_dec(v_a_1264_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1294_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___y_1274_; 
switch(lean_obj_tag(v_fst_1268_))
{
case 0:
{
lean_object* v_e_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1289_; 
lean_del_object(v___x_1271_);
lean_del_object(v___x_1266_);
lean_dec_ref(v_e_1255_);
lean_dec_ref(v_post_1251_);
lean_dec_ref(v_pre_1250_);
v_e_1281_ = lean_ctor_get(v_fst_1268_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_fst_1268_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1283_ = v_fst_1268_;
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_e_1281_);
lean_dec(v_fst_1268_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v_e_1281_);
lean_ctor_set(v___x_1285_, 1, v_snd_1269_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1285_);
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
case 1:
{
lean_object* v_e_1290_; lean_object* v___x_1291_; 
lean_del_object(v___x_1271_);
lean_del_object(v___x_1266_);
lean_dec_ref(v_e_1255_);
v_e_1290_ = lean_ctor_get(v_fst_1268_, 0);
lean_inc_ref(v_e_1290_);
lean_dec_ref_known(v_fst_1268_, 1);
v___x_1291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1250_, v_post_1251_, v_usedLetOnly_1252_, v_skipConstInApp_1253_, v_skipInstances_1254_, v_e_1290_, v_a_1256_, v_snd_1269_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
return v___x_1291_;
}
default: 
{
lean_object* v_e_x3f_1292_; 
lean_dec_ref(v_post_1251_);
lean_dec_ref(v_pre_1250_);
v_e_x3f_1292_ = lean_ctor_get(v_fst_1268_, 0);
lean_inc(v_e_x3f_1292_);
lean_dec_ref_known(v_fst_1268_, 1);
if (lean_obj_tag(v_e_x3f_1292_) == 0)
{
v___y_1274_ = v_e_1255_;
goto v___jp_1273_;
}
else
{
lean_object* v_val_1293_; 
lean_dec_ref(v_e_1255_);
v_val_1293_ = lean_ctor_get(v_e_x3f_1292_, 0);
lean_inc(v_val_1293_);
lean_dec_ref_known(v_e_x3f_1292_, 1);
v___y_1274_ = v_val_1293_;
goto v___jp_1273_;
}
}
}
v___jp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___y_1274_);
v___x_1276_ = v___x_1271_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___y_1274_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_snd_1269_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1276_);
v___x_1278_ = v___x_1266_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
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
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_e_1255_);
lean_dec_ref(v_post_1251_);
lean_dec_ref(v_pre_1250_);
v_a_1296_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1263_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1263_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1250_ = stack[0].m_obj;
lean_object* v_post_1251_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1252_ = stack[2].m_num;
uint8_t v_skipConstInApp_1253_ = stack[3].m_num;
uint8_t v_skipInstances_1254_ = stack[4].m_num;
lean_object* v_e_1255_ = stack[5].m_obj;
lean_object* v_a_1256_ = stack[6].m_obj;
lean_object* v___y_1257_ = stack[7].m_obj;
lean_object* v___y_1258_ = stack[8].m_obj;
lean_object* v___y_1259_ = stack[9].m_obj;
lean_object* v___y_1260_ = stack[10].m_obj;
lean_object* v___y_1261_ = stack[11].m_obj;
lean_object* v_res_1304_;
v_res_1304_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1250_, v_post_1251_, v_usedLetOnly_1252_, v_skipConstInApp_1253_, v_skipInstances_1254_, v_e_1255_, v_a_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
stack->m_obj
 = v_res_1304_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1305_, lean_object* v_post_1306_, uint8_t v_usedLetOnly_1307_, uint8_t v_skipConstInApp_1308_, uint8_t v_skipInstances_1309_, lean_object* v_fvars_1310_, lean_object* v_e_1311_, lean_object* v_a_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
if (lean_obj_tag(v_e_1311_) == 6)
{
lean_object* v_binderName_1319_; lean_object* v_binderType_1320_; lean_object* v_body_1321_; uint8_t v_binderInfo_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_binderName_1319_ = lean_ctor_get(v_e_1311_, 0);
lean_inc(v_binderName_1319_);
v_binderType_1320_ = lean_ctor_get(v_e_1311_, 1);
lean_inc_ref(v_binderType_1320_);
v_body_1321_ = lean_ctor_get(v_e_1311_, 2);
lean_inc_ref(v_body_1321_);
v_binderInfo_1322_ = lean_ctor_get_uint8(v_e_1311_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1311_, 3);
v___x_1323_ = lean_box(v_usedLetOnly_1307_);
v___x_1324_ = lean_box(v_skipConstInApp_1308_);
v___x_1325_ = lean_box(v_skipInstances_1309_);
lean_inc_ref(v_post_1306_);
lean_inc_ref(v_pre_1305_);
lean_inc_ref(v_fvars_1310_);
v___f_1326_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1326_, 0, v_fvars_1310_);
lean_closure_set(v___f_1326_, 1, v_pre_1305_);
lean_closure_set(v___f_1326_, 2, v_post_1306_);
lean_closure_set(v___f_1326_, 3, v___x_1323_);
lean_closure_set(v___f_1326_, 4, v___x_1324_);
lean_closure_set(v___f_1326_, 5, v___x_1325_);
lean_closure_set(v___f_1326_, 6, v_body_1321_);
v___x_1327_ = lean_expr_instantiate_rev(v_binderType_1320_, v_fvars_1310_);
lean_dec_ref(v_fvars_1310_);
lean_dec_ref(v_binderType_1320_);
v___x_1328_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1305_, v_post_1306_, v_usedLetOnly_1307_, v_skipConstInApp_1308_, v_skipInstances_1309_, v___x_1327_, v_a_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v_fst_1330_; lean_object* v_snd_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v_fst_1330_ = lean_ctor_get(v_a_1329_, 0);
lean_inc(v_fst_1330_);
v_snd_1331_ = lean_ctor_get(v_a_1329_, 1);
lean_inc(v_snd_1331_);
lean_dec(v_a_1329_);
v___x_1332_ = 0;
v___x_1333_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1319_, v_binderInfo_1322_, v_fst_1330_, v___f_1326_, v___x_1332_, v_a_1312_, v_snd_1331_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1333_;
}
else
{
lean_dec_ref(v___f_1326_);
lean_dec(v_binderName_1319_);
return v___x_1328_;
}
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_expr_instantiate_rev(v_e_1311_, v_fvars_1310_);
lean_dec_ref(v_e_1311_);
lean_inc_ref(v_post_1306_);
lean_inc_ref(v_pre_1305_);
v___x_1335_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1305_, v_post_1306_, v_usedLetOnly_1307_, v_skipConstInApp_1308_, v_skipInstances_1309_, v___x_1334_, v_a_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v_fst_1337_; lean_object* v_snd_1338_; uint8_t v___x_1339_; uint8_t v___x_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v_fst_1337_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_fst_1337_);
v_snd_1338_ = lean_ctor_get(v_a_1336_, 1);
lean_inc(v_snd_1338_);
lean_dec(v_a_1336_);
v___x_1339_ = 0;
v___x_1340_ = 1;
v___x_1341_ = 1;
v___x_1342_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1310_, v_fst_1337_, v___x_1339_, v_usedLetOnly_1307_, v___x_1339_, v___x_1340_, v___x_1341_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec_ref(v_fvars_1310_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1305_, v_post_1306_, v_usedLetOnly_1307_, v_skipConstInApp_1308_, v_skipInstances_1309_, v_a_1343_, v_a_1312_, v_snd_1338_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1344_;
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_snd_1338_);
lean_dec_ref(v_post_1306_);
lean_dec_ref(v_pre_1305_);
v_a_1345_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1342_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1342_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1310_);
lean_dec_ref(v_post_1306_);
lean_dec_ref(v_pre_1305_);
return v___x_1335_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1305_ = stack[0].m_obj;
lean_object* v_post_1306_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1307_ = stack[2].m_num;
uint8_t v_skipConstInApp_1308_ = stack[3].m_num;
uint8_t v_skipInstances_1309_ = stack[4].m_num;
lean_object* v_fvars_1310_ = stack[5].m_obj;
lean_object* v_e_1311_ = stack[6].m_obj;
lean_object* v_a_1312_ = stack[7].m_obj;
lean_object* v___y_1313_ = stack[8].m_obj;
lean_object* v___y_1314_ = stack[9].m_obj;
lean_object* v___y_1315_ = stack[10].m_obj;
lean_object* v___y_1316_ = stack[11].m_obj;
lean_object* v___y_1317_ = stack[12].m_obj;
lean_object* v_res_1353_;
v_res_1353_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1305_, v_post_1306_, v_usedLetOnly_1307_, v_skipConstInApp_1308_, v_skipInstances_1309_, v_fvars_1310_, v_e_1311_, v_a_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
stack->m_obj
 = v_res_1353_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1354_, lean_object* v_pre_1355_, lean_object* v_post_1356_, uint8_t v_usedLetOnly_1357_, uint8_t v_skipConstInApp_1358_, uint8_t v_skipInstances_1359_, lean_object* v_body_1360_, lean_object* v_x_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_array_push(v_fvars_1354_, v_x_1361_);
v___x_1370_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1355_, v_post_1356_, v_usedLetOnly_1357_, v_skipConstInApp_1358_, v_skipInstances_1359_, v___x_1369_, v_body_1360_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1370_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1354_ = stack[0].m_obj;
lean_object* v_pre_1355_ = stack[1].m_obj;
lean_object* v_post_1356_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1357_ = stack[3].m_num;
uint8_t v_skipConstInApp_1358_ = stack[4].m_num;
uint8_t v_skipInstances_1359_ = stack[5].m_num;
lean_object* v_body_1360_ = stack[6].m_obj;
lean_object* v_x_1361_ = stack[7].m_obj;
lean_object* v___y_1362_ = stack[8].m_obj;
lean_object* v___y_1363_ = stack[9].m_obj;
lean_object* v___y_1364_ = stack[10].m_obj;
lean_object* v___y_1365_ = stack[11].m_obj;
lean_object* v___y_1366_ = stack[12].m_obj;
lean_object* v___y_1367_ = stack[13].m_obj;
lean_object* v_res_1371_;
v_res_1371_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1354_, v_pre_1355_, v_post_1356_, v_usedLetOnly_1357_, v_skipConstInApp_1358_, v_skipInstances_1359_, v_body_1360_, v_x_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
stack->m_obj
 = v_res_1371_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1372_, lean_object* v_pre_1373_, lean_object* v_post_1374_, lean_object* v_usedLetOnly_1375_, lean_object* v_skipConstInApp_1376_, lean_object* v_skipInstances_1377_, lean_object* v_body_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v_usedLetOnly_boxed_1387_; uint8_t v_skipConstInApp_boxed_1388_; uint8_t v_skipInstances_boxed_1389_; lean_object* v_res_1390_; 
v_usedLetOnly_boxed_1387_ = lean_unbox(v_usedLetOnly_1375_);
v_skipConstInApp_boxed_1388_ = lean_unbox(v_skipConstInApp_1376_);
v_skipInstances_boxed_1389_ = lean_unbox(v_skipInstances_1377_);
v_res_1390_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1372_, v_pre_1373_, v_post_1374_, v_usedLetOnly_boxed_1387_, v_skipConstInApp_boxed_1388_, v_skipInstances_boxed_1389_, v_body_1378_, v_x_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1380_);
return v_res_1390_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1391_, lean_object* v_post_1392_, uint8_t v_usedLetOnly_1393_, uint8_t v_skipConstInApp_1394_, uint8_t v_skipInstances_1395_, lean_object* v_fvars_1396_, lean_object* v_e_1397_, lean_object* v_a_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
if (lean_obj_tag(v_e_1397_) == 8)
{
lean_object* v_declName_1405_; lean_object* v_type_1406_; lean_object* v_value_1407_; lean_object* v_body_1408_; uint8_t v_nondep_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___f_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_declName_1405_ = lean_ctor_get(v_e_1397_, 0);
lean_inc(v_declName_1405_);
v_type_1406_ = lean_ctor_get(v_e_1397_, 1);
lean_inc_ref(v_type_1406_);
v_value_1407_ = lean_ctor_get(v_e_1397_, 2);
lean_inc_ref(v_value_1407_);
v_body_1408_ = lean_ctor_get(v_e_1397_, 3);
lean_inc_ref(v_body_1408_);
v_nondep_1409_ = lean_ctor_get_uint8(v_e_1397_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1397_, 4);
v___x_1410_ = lean_box(v_usedLetOnly_1393_);
v___x_1411_ = lean_box(v_skipConstInApp_1394_);
v___x_1412_ = lean_box(v_skipInstances_1395_);
lean_inc_ref_n(v_post_1392_, 2);
lean_inc_ref_n(v_pre_1391_, 2);
lean_inc_ref(v_fvars_1396_);
v___f_1413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1413_, 0, v_fvars_1396_);
lean_closure_set(v___f_1413_, 1, v_pre_1391_);
lean_closure_set(v___f_1413_, 2, v_post_1392_);
lean_closure_set(v___f_1413_, 3, v___x_1410_);
lean_closure_set(v___f_1413_, 4, v___x_1411_);
lean_closure_set(v___f_1413_, 5, v___x_1412_);
lean_closure_set(v___f_1413_, 6, v_body_1408_);
v___x_1414_ = lean_expr_instantiate_rev(v_type_1406_, v_fvars_1396_);
lean_dec_ref(v_type_1406_);
v___x_1415_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1391_, v_post_1392_, v_usedLetOnly_1393_, v_skipConstInApp_1394_, v_skipInstances_1395_, v___x_1414_, v_a_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v_fst_1417_; lean_object* v_snd_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v_fst_1417_ = lean_ctor_get(v_a_1416_, 0);
lean_inc(v_fst_1417_);
v_snd_1418_ = lean_ctor_get(v_a_1416_, 1);
lean_inc(v_snd_1418_);
lean_dec(v_a_1416_);
v___x_1419_ = lean_expr_instantiate_rev(v_value_1407_, v_fvars_1396_);
lean_dec_ref(v_fvars_1396_);
lean_dec_ref(v_value_1407_);
v___x_1420_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1391_, v_post_1392_, v_usedLetOnly_1393_, v_skipConstInApp_1394_, v_skipInstances_1395_, v___x_1419_, v_a_1398_, v_snd_1418_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v_fst_1422_; lean_object* v_snd_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v_fst_1422_ = lean_ctor_get(v_a_1421_, 0);
lean_inc(v_fst_1422_);
v_snd_1423_ = lean_ctor_get(v_a_1421_, 1);
lean_inc(v_snd_1423_);
lean_dec(v_a_1421_);
v___x_1424_ = 0;
v___x_1425_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1405_, v_fst_1417_, v_fst_1422_, v___f_1413_, v_nondep_1409_, v___x_1424_, v_a_1398_, v_snd_1423_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
return v___x_1425_;
}
else
{
lean_dec(v_fst_1417_);
lean_dec_ref(v___f_1413_);
lean_dec(v_declName_1405_);
return v___x_1420_;
}
}
else
{
lean_dec_ref(v___f_1413_);
lean_dec_ref(v_value_1407_);
lean_dec(v_declName_1405_);
lean_dec_ref(v_fvars_1396_);
lean_dec_ref(v_post_1392_);
lean_dec_ref(v_pre_1391_);
return v___x_1415_;
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_expr_instantiate_rev(v_e_1397_, v_fvars_1396_);
lean_dec_ref(v_e_1397_);
lean_inc_ref(v_post_1392_);
lean_inc_ref(v_pre_1391_);
v___x_1427_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1391_, v_post_1392_, v_usedLetOnly_1393_, v_skipConstInApp_1394_, v_skipInstances_1395_, v___x_1426_, v_a_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v_fst_1429_; lean_object* v_snd_1430_; uint8_t v___x_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v_fst_1429_ = lean_ctor_get(v_a_1428_, 0);
lean_inc(v_fst_1429_);
v_snd_1430_ = lean_ctor_get(v_a_1428_, 1);
lean_inc(v_snd_1430_);
lean_dec(v_a_1428_);
v___x_1431_ = 0;
v___x_1432_ = 1;
v___x_1433_ = l_Lean_Meta_mkLetFVars(v_fvars_1396_, v_fst_1429_, v_usedLetOnly_1393_, v___x_1431_, v___x_1432_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec_ref(v_fvars_1396_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1391_, v_post_1392_, v_usedLetOnly_1393_, v_skipConstInApp_1394_, v_skipInstances_1395_, v_a_1434_, v_a_1398_, v_snd_1430_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
return v___x_1435_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_snd_1430_);
lean_dec_ref(v_post_1392_);
lean_dec_ref(v_pre_1391_);
v_a_1436_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1433_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1433_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1396_);
lean_dec_ref(v_post_1392_);
lean_dec_ref(v_pre_1391_);
return v___x_1427_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1391_ = stack[0].m_obj;
lean_object* v_post_1392_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1393_ = stack[2].m_num;
uint8_t v_skipConstInApp_1394_ = stack[3].m_num;
uint8_t v_skipInstances_1395_ = stack[4].m_num;
lean_object* v_fvars_1396_ = stack[5].m_obj;
lean_object* v_e_1397_ = stack[6].m_obj;
lean_object* v_a_1398_ = stack[7].m_obj;
lean_object* v___y_1399_ = stack[8].m_obj;
lean_object* v___y_1400_ = stack[9].m_obj;
lean_object* v___y_1401_ = stack[10].m_obj;
lean_object* v___y_1402_ = stack[11].m_obj;
lean_object* v___y_1403_ = stack[12].m_obj;
lean_object* v_res_1444_;
v_res_1444_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1391_, v_post_1392_, v_usedLetOnly_1393_, v_skipConstInApp_1394_, v_skipInstances_1395_, v_fvars_1396_, v_e_1397_, v_a_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
stack->m_obj
 = v_res_1444_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_pre_1445_, lean_object* v_post_1446_, uint8_t v_usedLetOnly_1447_, uint8_t v_skipConstInApp_1448_, uint8_t v_skipInstances_1449_, size_t v_sz_1450_, size_t v_i_1451_, lean_object* v_bs_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_usize_dec_lt(v_i_1451_, v_sz_1450_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v_post_1446_);
lean_dec_ref(v_pre_1445_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v_bs_1452_);
lean_ctor_set(v___x_1461_, 1, v___y_1454_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
else
{
lean_object* v_v_1463_; lean_object* v___x_1464_; lean_object* v_bs_x27_1465_; lean_object* v___x_1466_; 
v_v_1463_ = lean_array_uget(v_bs_1452_, v_i_1451_);
v___x_1464_ = lean_unsigned_to_nat(0u);
v_bs_x27_1465_ = lean_array_uset(v_bs_1452_, v_i_1451_, v___x_1464_);
lean_inc_ref(v_post_1446_);
lean_inc_ref(v_pre_1445_);
v___x_1466_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1445_, v_post_1446_, v_usedLetOnly_1447_, v_skipConstInApp_1448_, v_skipInstances_1449_, v_v_1463_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v_fst_1468_; lean_object* v_snd_1469_; size_t v___x_1470_; size_t v___x_1471_; lean_object* v___x_1472_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v_fst_1468_ = lean_ctor_get(v_a_1467_, 0);
lean_inc(v_fst_1468_);
v_snd_1469_ = lean_ctor_get(v_a_1467_, 1);
lean_inc(v_snd_1469_);
lean_dec(v_a_1467_);
v___x_1470_ = ((size_t)1ULL);
v___x_1471_ = lean_usize_add(v_i_1451_, v___x_1470_);
v___x_1472_ = lean_array_uset(v_bs_x27_1465_, v_i_1451_, v_fst_1468_);
v_i_1451_ = v___x_1471_;
v_bs_1452_ = v___x_1472_;
v___y_1454_ = v_snd_1469_;
goto _start;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec_ref(v_bs_x27_1465_);
lean_dec_ref(v_post_1446_);
lean_dec_ref(v_pre_1445_);
v_a_1474_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1466_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1466_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1445_ = stack[0].m_obj;
lean_object* v_post_1446_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1447_ = stack[2].m_num;
uint8_t v_skipConstInApp_1448_ = stack[3].m_num;
uint8_t v_skipInstances_1449_ = stack[4].m_num;
size_t v_sz_1450_ = stack[5].m_num;
size_t v_i_1451_ = stack[6].m_num;
lean_object* v_bs_1452_ = stack[7].m_obj;
lean_object* v___y_1453_ = stack[8].m_obj;
lean_object* v___y_1454_ = stack[9].m_obj;
lean_object* v___y_1455_ = stack[10].m_obj;
lean_object* v___y_1456_ = stack[11].m_obj;
lean_object* v___y_1457_ = stack[12].m_obj;
lean_object* v___y_1458_ = stack[13].m_obj;
lean_object* v_res_1482_;
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1445_, v_post_1446_, v_usedLetOnly_1447_, v_skipConstInApp_1448_, v_skipInstances_1449_, v_sz_1450_, v_i_1451_, v_bs_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
stack->m_obj
 = v_res_1482_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object* v_pre_1483_, lean_object* v_post_1484_, uint8_t v_usedLetOnly_1485_, uint8_t v_skipConstInApp_1486_, uint8_t v_skipInstances_1487_, lean_object* v___x_1488_, lean_object* v___y_1489_, lean_object* v_b_1490_, lean_object* v_a_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1483_, v_post_1484_, v_usedLetOnly_1485_, v_skipConstInApp_1486_, v_skipInstances_1487_, v___x_1488_, v___y_1489_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1517_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1517_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1517_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_fst_1503_; lean_object* v_snd_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1516_; 
v_fst_1503_ = lean_ctor_get(v_a_1499_, 0);
v_snd_1504_ = lean_ctor_get(v_a_1499_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_a_1499_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1506_ = v_a_1499_;
v_isShared_1507_ = v_isSharedCheck_1516_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_snd_1504_);
lean_inc(v_fst_1503_);
lean_dec(v_a_1499_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1516_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1508_ = lean_array_fset(v_b_1490_, v_a_1491_, v_fst_1503_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1509_);
v___x_1511_ = v___x_1506_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_snd_1504_);
v___x_1511_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1513_; 
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1511_);
v___x_1513_ = v___x_1501_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec_ref(v_b_1490_);
v_a_1518_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1498_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1498_);
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
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1483_ = stack[0].m_obj;
lean_object* v_post_1484_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1485_ = stack[2].m_num;
uint8_t v_skipConstInApp_1486_ = stack[3].m_num;
uint8_t v_skipInstances_1487_ = stack[4].m_num;
lean_object* v___x_1488_ = stack[5].m_obj;
lean_object* v___y_1489_ = stack[6].m_obj;
lean_object* v_b_1490_ = stack[7].m_obj;
lean_object* v_a_1491_ = stack[8].m_obj;
lean_object* v___y_1492_ = stack[9].m_obj;
lean_object* v___y_1493_ = stack[10].m_obj;
lean_object* v___y_1494_ = stack[11].m_obj;
lean_object* v___y_1495_ = stack[12].m_obj;
lean_object* v___y_1496_ = stack[13].m_obj;
lean_object* v_res_1526_;
v_res_1526_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1483_, v_post_1484_, v_usedLetOnly_1485_, v_skipConstInApp_1486_, v_skipInstances_1487_, v___x_1488_, v___y_1489_, v_b_1490_, v_a_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
stack->m_obj
 = v_res_1526_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v_pre_1527_, lean_object* v_post_1528_, lean_object* v_usedLetOnly_1529_, lean_object* v_skipConstInApp_1530_, lean_object* v_skipInstances_1531_, lean_object* v___x_1532_, lean_object* v___y_1533_, lean_object* v_b_1534_, lean_object* v_a_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v_usedLetOnly_boxed_1542_; uint8_t v_skipConstInApp_boxed_1543_; uint8_t v_skipInstances_boxed_1544_; lean_object* v_res_1545_; 
v_usedLetOnly_boxed_1542_ = lean_unbox(v_usedLetOnly_1529_);
v_skipConstInApp_boxed_1543_ = lean_unbox(v_skipConstInApp_1530_);
v_skipInstances_boxed_1544_ = lean_unbox(v_skipInstances_1531_);
v_res_1545_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1527_, v_post_1528_, v_usedLetOnly_boxed_1542_, v_skipConstInApp_boxed_1543_, v_skipInstances_boxed_1544_, v___x_1532_, v___y_1533_, v_b_1534_, v_a_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_a_1535_);
lean_dec(v___y_1533_);
return v_res_1545_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object* v_upperBound_1546_, lean_object* v___x_1547_, lean_object* v_pre_1548_, lean_object* v_post_1549_, uint8_t v_usedLetOnly_1550_, uint8_t v_skipConstInApp_1551_, uint8_t v_skipInstances_1552_, lean_object* v_a_1553_, lean_object* v_b_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___y_1563_; uint8_t v___x_1597_; 
v___x_1597_ = lean_nat_dec_lt(v_a_1553_, v_upperBound_1546_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec(v_a_1553_);
lean_dec_ref(v_post_1549_);
lean_dec_ref(v_pre_1548_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_b_1554_);
lean_ctor_set(v___x_1598_, 1, v___y_1556_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1600_ = lean_array_fget_borrowed(v_b_1554_, v_a_1553_);
v___x_1601_ = lean_array_get_size(v___x_1547_);
v___x_1602_ = lean_nat_dec_lt(v_a_1553_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___f_1606_; 
lean_inc(v___x_1600_);
v___x_1603_ = lean_box(v_usedLetOnly_1550_);
v___x_1604_ = lean_box(v_skipConstInApp_1551_);
v___x_1605_ = lean_box(v_skipInstances_1552_);
lean_inc(v_a_1553_);
lean_inc(v___y_1555_);
lean_inc_ref(v_post_1549_);
lean_inc_ref(v_pre_1548_);
v___f_1606_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1606_, 0, v_pre_1548_);
lean_closure_set(v___f_1606_, 1, v_post_1549_);
lean_closure_set(v___f_1606_, 2, v___x_1603_);
lean_closure_set(v___f_1606_, 3, v___x_1604_);
lean_closure_set(v___f_1606_, 4, v___x_1605_);
lean_closure_set(v___f_1606_, 5, v___x_1600_);
lean_closure_set(v___f_1606_, 6, v___y_1555_);
lean_closure_set(v___f_1606_, 7, v_b_1554_);
lean_closure_set(v___f_1606_, 8, v_a_1553_);
v___y_1563_ = v___f_1606_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1607_; uint8_t v_isInstance_1608_; 
v___x_1607_ = lean_array_fget_borrowed(v___x_1547_, v_a_1553_);
v_isInstance_1608_ = lean_ctor_get_uint8(v___x_1607_, sizeof(void*)*1 + 4);
if (v_isInstance_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___f_1612_; 
lean_inc(v___x_1600_);
v___x_1609_ = lean_box(v_usedLetOnly_1550_);
v___x_1610_ = lean_box(v_skipConstInApp_1551_);
v___x_1611_ = lean_box(v_skipInstances_1552_);
lean_inc(v_a_1553_);
lean_inc(v___y_1555_);
lean_inc_ref(v_post_1549_);
lean_inc_ref(v_pre_1548_);
v___f_1612_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1612_, 0, v_pre_1548_);
lean_closure_set(v___f_1612_, 1, v_post_1549_);
lean_closure_set(v___f_1612_, 2, v___x_1609_);
lean_closure_set(v___f_1612_, 3, v___x_1610_);
lean_closure_set(v___f_1612_, 4, v___x_1611_);
lean_closure_set(v___f_1612_, 5, v___x_1600_);
lean_closure_set(v___f_1612_, 6, v___y_1555_);
lean_closure_set(v___f_1612_, 7, v_b_1554_);
lean_closure_set(v___f_1612_, 8, v_a_1553_);
v___y_1563_ = v___f_1612_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1613_; lean_object* v___f_1614_; 
v___x_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_b_1554_);
v___f_1614_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1614_, 0, v___x_1613_);
v___y_1563_ = v___f_1614_;
goto v___jp_1562_;
}
}
}
v___jp_1562_:
{
lean_object* v___x_1564_; 
lean_inc(v___y_1560_);
lean_inc_ref(v___y_1559_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
v___x_1564_ = lean_apply_6(v___y_1563_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, lean_box(0));
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1588_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1588_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1588_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_fst_1569_; 
v_fst_1569_ = lean_ctor_get(v_a_1565_, 0);
lean_inc(v_fst_1569_);
if (lean_obj_tag(v_fst_1569_) == 0)
{
lean_object* v_snd_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1581_; 
lean_dec(v_a_1553_);
lean_dec_ref(v_post_1549_);
lean_dec_ref(v_pre_1548_);
v_snd_1570_ = lean_ctor_get(v_a_1565_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_a_1565_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; 
v_unused_1582_ = lean_ctor_get(v_a_1565_, 0);
lean_dec(v_unused_1582_);
v___x_1572_ = v_a_1565_;
v_isShared_1573_ = v_isSharedCheck_1581_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_snd_1570_);
lean_dec(v_a_1565_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1581_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_a_1574_; lean_object* v___x_1576_; 
v_a_1574_ = lean_ctor_get(v_fst_1569_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v_fst_1569_, 1);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v_a_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_snd_1570_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1576_);
v___x_1578_ = v___x_1567_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_snd_1583_; lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_del_object(v___x_1567_);
v_snd_1583_ = lean_ctor_get(v_a_1565_, 1);
lean_inc(v_snd_1583_);
lean_dec(v_a_1565_);
v_a_1584_ = lean_ctor_get(v_fst_1569_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v_fst_1569_, 1);
v___x_1585_ = lean_unsigned_to_nat(1u);
v___x_1586_ = lean_nat_add(v_a_1553_, v___x_1585_);
lean_dec(v_a_1553_);
v_a_1553_ = v___x_1586_;
v_b_1554_ = v_a_1584_;
v___y_1556_ = v_snd_1583_;
goto _start;
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_a_1553_);
lean_dec_ref(v_post_1549_);
lean_dec_ref(v_pre_1548_);
v_a_1589_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1564_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1564_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1546_ = stack[0].m_obj;
lean_object* v___x_1547_ = stack[1].m_obj;
lean_object* v_pre_1548_ = stack[2].m_obj;
lean_object* v_post_1549_ = stack[3].m_obj;
uint8_t v_usedLetOnly_1550_ = stack[4].m_num;
uint8_t v_skipConstInApp_1551_ = stack[5].m_num;
uint8_t v_skipInstances_1552_ = stack[6].m_num;
lean_object* v_a_1553_ = stack[7].m_obj;
lean_object* v_b_1554_ = stack[8].m_obj;
lean_object* v___y_1555_ = stack[9].m_obj;
lean_object* v___y_1556_ = stack[10].m_obj;
lean_object* v___y_1557_ = stack[11].m_obj;
lean_object* v___y_1558_ = stack[12].m_obj;
lean_object* v___y_1559_ = stack[13].m_obj;
lean_object* v___y_1560_ = stack[14].m_obj;
lean_object* v_res_1615_;
v_res_1615_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_1546_, v___x_1547_, v_pre_1548_, v_post_1549_, v_usedLetOnly_1550_, v_skipConstInApp_1551_, v_skipInstances_1552_, v_a_1553_, v_b_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
stack->m_obj
 = v_res_1615_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1616_, lean_object* v_pre_1617_, lean_object* v_post_1618_, uint8_t v_usedLetOnly_1619_, uint8_t v_skipConstInApp_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_f_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; 
if (lean_obj_tag(v_x_1621_) == 5)
{
lean_object* v_fn_1687_; lean_object* v_arg_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_fn_1687_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_fn_1687_);
v_arg_1688_ = lean_ctor_get(v_x_1621_, 1);
lean_inc_ref(v_arg_1688_);
lean_dec_ref_known(v_x_1621_, 2);
v___x_1689_ = lean_array_set(v_x_1622_, v_x_1623_, v_arg_1688_);
v___x_1690_ = lean_unsigned_to_nat(1u);
v___x_1691_ = lean_nat_sub(v_x_1623_, v___x_1690_);
lean_dec(v_x_1623_);
v_x_1621_ = v_fn_1687_;
v_x_1622_ = v___x_1689_;
v_x_1623_ = v___x_1691_;
goto _start;
}
else
{
lean_dec(v_x_1623_);
if (v_skipConstInApp_1620_ == 0)
{
goto v___jp_1682_;
}
else
{
uint8_t v___x_1693_; 
v___x_1693_ = l_Lean_Expr_isConst(v_x_1621_);
if (v___x_1693_ == 0)
{
goto v___jp_1682_;
}
else
{
v_f_1632_ = v_x_1621_;
v___y_1633_ = v___y_1624_;
v___y_1634_ = v___y_1625_;
v___y_1635_ = v___y_1626_;
v___y_1636_ = v___y_1627_;
v___y_1637_ = v___y_1628_;
v___y_1638_ = v___y_1629_;
goto v___jp_1631_;
}
}
}
v___jp_1631_:
{
if (v_skipInstances_1616_ == 0)
{
size_t v_sz_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v_sz_1639_ = lean_array_size(v_x_1622_);
v___x_1640_ = ((size_t)0ULL);
lean_inc_ref(v_post_1618_);
lean_inc_ref(v_pre_1617_);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1617_, v_post_1618_, v_usedLetOnly_1619_, v_skipConstInApp_1620_, v_skipInstances_1616_, v_sz_1639_, v___x_1640_, v_x_1622_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
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
v___x_1645_ = l_Lean_mkAppN(v_f_1632_, v_fst_1643_);
lean_dec(v_fst_1643_);
v___x_1646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1617_, v_post_1618_, v_usedLetOnly_1619_, v_skipConstInApp_1620_, v_skipInstances_1616_, v___x_1645_, v___y_1633_, v_snd_1644_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
return v___x_1646_;
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref(v_f_1632_);
lean_dec_ref(v_post_1618_);
lean_dec_ref(v_pre_1617_);
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
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_array_get_size(v_x_1622_);
lean_inc_ref(v_f_1632_);
v___x_1656_ = l_Lean_Meta_getFunInfoNArgs(v_f_1632_, v___x_1655_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v_paramInfo_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v_paramInfo_1658_ = lean_ctor_get(v_a_1657_, 0);
lean_inc_ref(v_paramInfo_1658_);
lean_dec(v_a_1657_);
v___x_1659_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1618_);
lean_inc_ref(v_pre_1617_);
v___x_1660_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_1655_, v_paramInfo_1658_, v_pre_1617_, v_post_1618_, v_usedLetOnly_1619_, v_skipConstInApp_1620_, v_skipInstances_1616_, v___x_1659_, v_x_1622_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec_ref(v_paramInfo_1658_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v_fst_1662_; lean_object* v_snd_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v_fst_1662_ = lean_ctor_get(v_a_1661_, 0);
lean_inc(v_fst_1662_);
v_snd_1663_ = lean_ctor_get(v_a_1661_, 1);
lean_inc(v_snd_1663_);
lean_dec(v_a_1661_);
v___x_1664_ = l_Lean_mkAppN(v_f_1632_, v_fst_1662_);
lean_dec(v_fst_1662_);
v___x_1665_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1617_, v_post_1618_, v_usedLetOnly_1619_, v_skipConstInApp_1620_, v_skipInstances_1616_, v___x_1664_, v___y_1633_, v_snd_1663_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
return v___x_1665_;
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v_f_1632_);
lean_dec_ref(v_post_1618_);
lean_dec_ref(v_pre_1617_);
v_a_1666_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1660_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1660_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v___y_1634_);
lean_dec_ref(v_f_1632_);
lean_dec_ref(v_x_1622_);
lean_dec_ref(v_post_1618_);
lean_dec_ref(v_pre_1617_);
v_a_1674_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1656_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1656_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
v___jp_1682_:
{
lean_object* v___x_1683_; 
lean_inc_ref(v_post_1618_);
lean_inc_ref(v_pre_1617_);
v___x_1683_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1617_, v_post_1618_, v_usedLetOnly_1619_, v_skipConstInApp_1620_, v_skipInstances_1616_, v_x_1621_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v_fst_1685_; lean_object* v_snd_1686_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v_fst_1685_ = lean_ctor_get(v_a_1684_, 0);
lean_inc(v_fst_1685_);
v_snd_1686_ = lean_ctor_get(v_a_1684_, 1);
lean_inc(v_snd_1686_);
lean_dec(v_a_1684_);
v_f_1632_ = v_fst_1685_;
v___y_1633_ = v___y_1624_;
v___y_1634_ = v_snd_1686_;
v___y_1635_ = v___y_1626_;
v___y_1636_ = v___y_1627_;
v___y_1637_ = v___y_1628_;
v___y_1638_ = v___y_1629_;
goto v___jp_1631_;
}
else
{
lean_dec_ref(v_x_1622_);
lean_dec_ref(v_post_1618_);
lean_dec_ref(v_pre_1617_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_1616_ = stack[0].m_num;
lean_object* v_pre_1617_ = stack[1].m_obj;
lean_object* v_post_1618_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1619_ = stack[3].m_num;
uint8_t v_skipConstInApp_1620_ = stack[4].m_num;
lean_object* v_x_1621_ = stack[5].m_obj;
lean_object* v_x_1622_ = stack[6].m_obj;
lean_object* v_x_1623_ = stack[7].m_obj;
lean_object* v___y_1624_ = stack[8].m_obj;
lean_object* v___y_1625_ = stack[9].m_obj;
lean_object* v___y_1626_ = stack[10].m_obj;
lean_object* v___y_1627_ = stack[11].m_obj;
lean_object* v___y_1628_ = stack[12].m_obj;
lean_object* v___y_1629_ = stack[13].m_obj;
lean_object* v_res_1694_;
v_res_1694_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1616_, v_pre_1617_, v_post_1618_, v_usedLetOnly_1619_, v_skipConstInApp_1620_, v_x_1621_, v_x_1622_, v_x_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
stack->m_obj
 = v_res_1694_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1695_, lean_object* v_pre_1696_, lean_object* v_e_1697_, lean_object* v_post_1698_, uint8_t v_usedLetOnly_1699_, uint8_t v_skipConstInApp_1700_, uint8_t v_skipInstances_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_Core_checkSystem(v___x_1695_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v___x_1710_; 
lean_dec_ref_known(v___x_1709_, 1);
lean_inc_ref(v_pre_1696_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc_ref(v_e_1697_);
v___x_1710_ = lean_apply_7(v_pre_1696_, v_e_1697_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, lean_box(0));
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1772_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1772_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1772_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_fst_1715_; lean_object* v_snd_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1771_; 
v_fst_1715_ = lean_ctor_get(v_a_1711_, 0);
v_snd_1716_ = lean_ctor_get(v_a_1711_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_a_1711_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1718_ = v_a_1711_;
v_isShared_1719_ = v_isSharedCheck_1771_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_snd_1716_);
lean_inc(v_fst_1715_);
lean_dec(v_a_1711_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1771_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___y_1721_; 
switch(lean_obj_tag(v_fst_1715_))
{
case 0:
{
lean_object* v_e_1760_; lean_object* v___x_1762_; 
lean_dec_ref(v_post_1698_);
lean_dec_ref(v_e_1697_);
lean_dec_ref(v_pre_1696_);
v_e_1760_ = lean_ctor_get(v_fst_1715_, 0);
lean_inc_ref(v_e_1760_);
lean_dec_ref_known(v_fst_1715_, 1);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v_e_1760_);
v___x_1762_ = v___x_1718_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_e_1760_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_snd_1716_);
v___x_1762_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1764_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1762_);
v___x_1764_ = v___x_1713_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
case 1:
{
lean_object* v_e_1767_; lean_object* v___x_1768_; 
lean_del_object(v___x_1718_);
lean_del_object(v___x_1713_);
lean_dec_ref(v_e_1697_);
v_e_1767_ = lean_ctor_get(v_fst_1715_, 0);
lean_inc_ref(v_e_1767_);
lean_dec_ref_known(v_fst_1715_, 1);
v___x_1768_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v_e_1767_, v___y_1702_, v_snd_1716_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1768_;
}
default: 
{
lean_object* v_e_x3f_1769_; 
lean_del_object(v___x_1718_);
lean_del_object(v___x_1713_);
v_e_x3f_1769_ = lean_ctor_get(v_fst_1715_, 0);
lean_inc(v_e_x3f_1769_);
lean_dec_ref_known(v_fst_1715_, 1);
if (lean_obj_tag(v_e_x3f_1769_) == 0)
{
v___y_1721_ = v_e_1697_;
goto v___jp_1720_;
}
else
{
lean_object* v_val_1770_; 
lean_dec_ref(v_e_1697_);
v_val_1770_ = lean_ctor_get(v_e_x3f_1769_, 0);
lean_inc(v_val_1770_);
lean_dec_ref_known(v_e_x3f_1769_, 1);
v___y_1721_ = v_val_1770_;
goto v___jp_1720_;
}
}
}
v___jp_1720_:
{
switch(lean_obj_tag(v___y_1721_))
{
case 7:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1723_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v___x_1722_, v___y_1721_, v___y_1702_, v_snd_1716_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1723_;
}
case 6:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1725_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v___x_1724_, v___y_1721_, v___y_1702_, v_snd_1716_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1725_;
}
case 8:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1727_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v___x_1726_, v___y_1721_, v___y_1702_, v_snd_1716_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1727_;
}
case 5:
{
lean_object* v_dummy_1728_; lean_object* v_nargs_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_dummy_1728_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1729_ = l_Lean_Expr_getAppNumArgs(v___y_1721_);
lean_inc(v_nargs_1729_);
v___x_1730_ = lean_mk_array(v_nargs_1729_, v_dummy_1728_);
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_nat_sub(v_nargs_1729_, v___x_1731_);
lean_dec(v_nargs_1729_);
v___x_1733_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1701_, v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v___y_1721_, v___x_1730_, v___x_1732_, v___y_1702_, v_snd_1716_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1733_;
}
case 10:
{
lean_object* v_data_1734_; lean_object* v_expr_1735_; lean_object* v___x_1736_; 
v_data_1734_ = lean_ctor_get(v___y_1721_, 0);
v_expr_1735_ = lean_ctor_get(v___y_1721_, 1);
lean_inc_ref(v_expr_1735_);
lean_inc_ref(v_post_1698_);
lean_inc_ref(v_pre_1696_);
v___x_1736_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v_expr_1735_, v___y_1702_, v_snd_1716_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
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
v___x_1740_ = lean_ptr_addr(v_expr_1735_);
v___x_1741_ = lean_ptr_addr(v_fst_1738_);
v___x_1742_ = lean_usize_dec_eq(v___x_1740_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_inc(v_data_1734_);
lean_dec_ref_known(v___y_1721_, 2);
v___x_1743_ = l_Lean_Expr_mdata___override(v_data_1734_, v_fst_1738_);
v___x_1744_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v___x_1743_, v___y_1702_, v_snd_1739_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; 
lean_dec(v_fst_1738_);
v___x_1745_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v___y_1721_, v___y_1702_, v_snd_1739_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1745_;
}
}
else
{
lean_dec_ref_known(v___y_1721_, 2);
lean_dec_ref(v_post_1698_);
lean_dec_ref(v_pre_1696_);
return v___x_1736_;
}
}
case 11:
{
lean_object* v_typeName_1746_; lean_object* v_idx_1747_; lean_object* v_struct_1748_; lean_object* v___x_1749_; 
v_typeName_1746_ = lean_ctor_get(v___y_1721_, 0);
v_idx_1747_ = lean_ctor_get(v___y_1721_, 1);
v_struct_1748_ = lean_ctor_get(v___y_1721_, 2);
lean_inc_ref(v_struct_1748_);
lean_inc_ref(v_post_1698_);
lean_inc_ref(v_pre_1696_);
v___x_1749_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v_struct_1748_, v___y_1702_, v_snd_1716_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v_fst_1751_; lean_object* v_snd_1752_; size_t v___x_1753_; size_t v___x_1754_; uint8_t v___x_1755_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v_fst_1751_ = lean_ctor_get(v_a_1750_, 0);
lean_inc(v_fst_1751_);
v_snd_1752_ = lean_ctor_get(v_a_1750_, 1);
lean_inc(v_snd_1752_);
lean_dec(v_a_1750_);
v___x_1753_ = lean_ptr_addr(v_struct_1748_);
v___x_1754_ = lean_ptr_addr(v_fst_1751_);
v___x_1755_ = lean_usize_dec_eq(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_inc(v_idx_1747_);
lean_inc(v_typeName_1746_);
lean_dec_ref_known(v___y_1721_, 3);
v___x_1756_ = l_Lean_Expr_proj___override(v_typeName_1746_, v_idx_1747_, v_fst_1751_);
v___x_1757_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v___x_1756_, v___y_1702_, v_snd_1752_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; 
lean_dec(v_fst_1751_);
v___x_1758_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v___y_1721_, v___y_1702_, v_snd_1752_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1758_;
}
}
else
{
lean_dec_ref_known(v___y_1721_, 3);
lean_dec_ref(v_post_1698_);
lean_dec_ref(v_pre_1696_);
return v___x_1749_;
}
}
default: 
{
lean_object* v___x_1759_; 
v___x_1759_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1696_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v___y_1721_, v___y_1702_, v_snd_1716_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1759_;
}
}
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_post_1698_);
lean_dec_ref(v_e_1697_);
lean_dec_ref(v_pre_1696_);
v_a_1773_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1710_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1710_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v___y_1703_);
lean_dec_ref(v_post_1698_);
lean_dec_ref(v_e_1697_);
lean_dec_ref(v_pre_1696_);
v_a_1781_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1709_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1709_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1695_ = stack[0].m_obj;
lean_object* v_pre_1696_ = stack[1].m_obj;
lean_object* v_e_1697_ = stack[2].m_obj;
lean_object* v_post_1698_ = stack[3].m_obj;
uint8_t v_usedLetOnly_1699_ = stack[4].m_num;
uint8_t v_skipConstInApp_1700_ = stack[5].m_num;
uint8_t v_skipInstances_1701_ = stack[6].m_num;
lean_object* v___y_1702_ = stack[7].m_obj;
lean_object* v___y_1703_ = stack[8].m_obj;
lean_object* v___y_1704_ = stack[9].m_obj;
lean_object* v___y_1705_ = stack[10].m_obj;
lean_object* v___y_1706_ = stack[11].m_obj;
lean_object* v___y_1707_ = stack[12].m_obj;
lean_object* v_res_1789_;
v_res_1789_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1695_, v_pre_1696_, v_e_1697_, v_post_1698_, v_usedLetOnly_1699_, v_skipConstInApp_1700_, v_skipInstances_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
stack->m_obj
 = v_res_1789_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1790_, lean_object* v_pre_1791_, lean_object* v_e_1792_, lean_object* v_post_1793_, lean_object* v_usedLetOnly_1794_, lean_object* v_skipConstInApp_1795_, lean_object* v_skipInstances_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
uint8_t v_usedLetOnly_boxed_1804_; uint8_t v_skipConstInApp_boxed_1805_; uint8_t v_skipInstances_boxed_1806_; lean_object* v_res_1807_; 
v_usedLetOnly_boxed_1804_ = lean_unbox(v_usedLetOnly_1794_);
v_skipConstInApp_boxed_1805_ = lean_unbox(v_skipConstInApp_1795_);
v_skipInstances_boxed_1806_ = lean_unbox(v_skipInstances_1796_);
v_res_1807_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1790_, v_pre_1791_, v_e_1792_, v_post_1793_, v_usedLetOnly_boxed_1804_, v_skipConstInApp_boxed_1805_, v_skipInstances_boxed_1806_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1797_);
return v_res_1807_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1808_, lean_object* v_post_1809_, uint8_t v_usedLetOnly_1810_, uint8_t v_skipConstInApp_1811_, uint8_t v_skipInstances_1812_, lean_object* v_e_1813_, lean_object* v_a_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_inc(v_a_1814_);
v___x_1821_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1821_, 0, lean_box(0));
lean_closure_set(v___x_1821_, 1, lean_box(0));
lean_closure_set(v___x_1821_, 2, v_a_1814_);
v___x_1822_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1821_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1877_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1877_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1877_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_fst_1827_; lean_object* v_snd_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1876_; 
v_fst_1827_ = lean_ctor_get(v_a_1823_, 0);
v_snd_1828_ = lean_ctor_get(v_a_1823_, 1);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_a_1823_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1830_ = v_a_1823_;
v_isShared_1831_ = v_isSharedCheck_1876_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_snd_1828_);
lean_inc(v_fst_1827_);
lean_dec(v_a_1823_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1876_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1827_, v_e_1813_);
lean_dec(v_fst_1827_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___f_1837_; lean_object* v___x_1838_; 
lean_del_object(v___x_1830_);
lean_del_object(v___x_1825_);
v___x_1833_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1834_ = lean_box(v_usedLetOnly_1810_);
v___x_1835_ = lean_box(v_skipConstInApp_1811_);
v___x_1836_ = lean_box(v_skipInstances_1812_);
lean_inc_ref(v_e_1813_);
v___f_1837_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1837_, 0, v___x_1833_);
lean_closure_set(v___f_1837_, 1, v_pre_1808_);
lean_closure_set(v___f_1837_, 2, v_e_1813_);
lean_closure_set(v___f_1837_, 3, v_post_1809_);
lean_closure_set(v___f_1837_, 4, v___x_1834_);
lean_closure_set(v___f_1837_, 5, v___x_1835_);
lean_closure_set(v___f_1837_, 6, v___x_1836_);
v___x_1838_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1837_, v_a_1814_, v_snd_1828_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v_fst_1840_; lean_object* v_snd_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
v_fst_1840_ = lean_ctor_get(v_a_1839_, 0);
lean_inc_n(v_fst_1840_, 2);
v_snd_1841_ = lean_ctor_get(v_a_1839_, 1);
lean_inc(v_snd_1841_);
lean_dec(v_a_1839_);
lean_inc(v_a_1814_);
v___f_1842_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1842_, 0, v_a_1814_);
lean_closure_set(v___f_1842_, 1, v_e_1813_);
lean_closure_set(v___f_1842_, 2, v_fst_1840_);
v___x_1843_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1842_, v_snd_1841_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1860_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1860_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1860_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v_snd_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1858_; 
v_snd_1848_ = lean_ctor_get(v_a_1844_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_a_1844_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v_a_1844_, 0);
lean_dec(v_unused_1859_);
v___x_1850_ = v_a_1844_;
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_snd_1848_);
lean_dec(v_a_1844_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_fst_1840_);
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_fst_1840_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_snd_1848_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1853_);
v___x_1855_ = v___x_1846_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
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
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_fst_1840_);
v_a_1861_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1843_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1843_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_dec_ref(v_e_1813_);
return v___x_1838_;
}
}
else
{
lean_object* v_val_1869_; lean_object* v___x_1871_; 
lean_dec_ref(v_e_1813_);
lean_dec_ref(v_post_1809_);
lean_dec_ref(v_pre_1808_);
v_val_1869_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v___x_1832_, 1);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v_val_1869_);
v___x_1871_ = v___x_1830_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_val_1869_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_snd_1828_);
v___x_1871_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1873_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1871_);
v___x_1873_ = v___x_1825_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec_ref(v_e_1813_);
lean_dec_ref(v_post_1809_);
lean_dec_ref(v_pre_1808_);
v_a_1878_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1822_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1822_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1808_ = stack[0].m_obj;
lean_object* v_post_1809_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1810_ = stack[2].m_num;
uint8_t v_skipConstInApp_1811_ = stack[3].m_num;
uint8_t v_skipInstances_1812_ = stack[4].m_num;
lean_object* v_e_1813_ = stack[5].m_obj;
lean_object* v_a_1814_ = stack[6].m_obj;
lean_object* v___y_1815_ = stack[7].m_obj;
lean_object* v___y_1816_ = stack[8].m_obj;
lean_object* v___y_1817_ = stack[9].m_obj;
lean_object* v___y_1818_ = stack[10].m_obj;
lean_object* v___y_1819_ = stack[11].m_obj;
lean_object* v_res_1886_;
v_res_1886_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1808_, v_post_1809_, v_usedLetOnly_1810_, v_skipConstInApp_1811_, v_skipInstances_1812_, v_e_1813_, v_a_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
stack->m_obj
 = v_res_1886_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1887_, lean_object* v_post_1888_, uint8_t v_usedLetOnly_1889_, uint8_t v_skipConstInApp_1890_, uint8_t v_skipInstances_1891_, lean_object* v_fvars_1892_, lean_object* v_e_1893_, lean_object* v_a_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
if (lean_obj_tag(v_e_1893_) == 7)
{
lean_object* v_binderName_1901_; lean_object* v_binderType_1902_; lean_object* v_body_1903_; uint8_t v_binderInfo_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___f_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_binderName_1901_ = lean_ctor_get(v_e_1893_, 0);
lean_inc(v_binderName_1901_);
v_binderType_1902_ = lean_ctor_get(v_e_1893_, 1);
lean_inc_ref(v_binderType_1902_);
v_body_1903_ = lean_ctor_get(v_e_1893_, 2);
lean_inc_ref(v_body_1903_);
v_binderInfo_1904_ = lean_ctor_get_uint8(v_e_1893_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1893_, 3);
v___x_1905_ = lean_box(v_usedLetOnly_1889_);
v___x_1906_ = lean_box(v_skipConstInApp_1890_);
v___x_1907_ = lean_box(v_skipInstances_1891_);
lean_inc_ref(v_post_1888_);
lean_inc_ref(v_pre_1887_);
lean_inc_ref(v_fvars_1892_);
v___f_1908_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1908_, 0, v_fvars_1892_);
lean_closure_set(v___f_1908_, 1, v_pre_1887_);
lean_closure_set(v___f_1908_, 2, v_post_1888_);
lean_closure_set(v___f_1908_, 3, v___x_1905_);
lean_closure_set(v___f_1908_, 4, v___x_1906_);
lean_closure_set(v___f_1908_, 5, v___x_1907_);
lean_closure_set(v___f_1908_, 6, v_body_1903_);
v___x_1909_ = lean_expr_instantiate_rev(v_binderType_1902_, v_fvars_1892_);
lean_dec_ref(v_fvars_1892_);
lean_dec_ref(v_binderType_1902_);
v___x_1910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1887_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v___x_1909_, v_a_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v_fst_1912_; lean_object* v_snd_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v_fst_1912_ = lean_ctor_get(v_a_1911_, 0);
lean_inc(v_fst_1912_);
v_snd_1913_ = lean_ctor_get(v_a_1911_, 1);
lean_inc(v_snd_1913_);
lean_dec(v_a_1911_);
v___x_1914_ = 0;
v___x_1915_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1901_, v_binderInfo_1904_, v_fst_1912_, v___f_1908_, v___x_1914_, v_a_1894_, v_snd_1913_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
return v___x_1915_;
}
else
{
lean_dec_ref(v___f_1908_);
lean_dec(v_binderName_1901_);
return v___x_1910_;
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_expr_instantiate_rev(v_e_1893_, v_fvars_1892_);
lean_dec_ref(v_e_1893_);
lean_inc_ref(v_post_1888_);
lean_inc_ref(v_pre_1887_);
v___x_1917_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1887_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v___x_1916_, v_a_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v_fst_1919_; lean_object* v_snd_1920_; uint8_t v___x_1921_; uint8_t v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v_fst_1919_ = lean_ctor_get(v_a_1918_, 0);
lean_inc(v_fst_1919_);
v_snd_1920_ = lean_ctor_get(v_a_1918_, 1);
lean_inc(v_snd_1920_);
lean_dec(v_a_1918_);
v___x_1921_ = 0;
v___x_1922_ = 1;
v___x_1923_ = 1;
v___x_1924_ = l_Lean_Meta_mkForallFVars(v_fvars_1892_, v_fst_1919_, v___x_1921_, v_usedLetOnly_1889_, v___x_1922_, v___x_1923_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec_ref(v_fvars_1892_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1887_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v_a_1925_, v_a_1894_, v_snd_1920_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
return v___x_1926_;
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec(v_snd_1920_);
lean_dec_ref(v_post_1888_);
lean_dec_ref(v_pre_1887_);
v_a_1927_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1924_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1924_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1892_);
lean_dec_ref(v_post_1888_);
lean_dec_ref(v_pre_1887_);
return v___x_1917_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1887_ = stack[0].m_obj;
lean_object* v_post_1888_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1889_ = stack[2].m_num;
uint8_t v_skipConstInApp_1890_ = stack[3].m_num;
uint8_t v_skipInstances_1891_ = stack[4].m_num;
lean_object* v_fvars_1892_ = stack[5].m_obj;
lean_object* v_e_1893_ = stack[6].m_obj;
lean_object* v_a_1894_ = stack[7].m_obj;
lean_object* v___y_1895_ = stack[8].m_obj;
lean_object* v___y_1896_ = stack[9].m_obj;
lean_object* v___y_1897_ = stack[10].m_obj;
lean_object* v___y_1898_ = stack[11].m_obj;
lean_object* v___y_1899_ = stack[12].m_obj;
lean_object* v_res_1935_;
v_res_1935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1887_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v_fvars_1892_, v_e_1893_, v_a_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
stack->m_obj
 = v_res_1935_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1936_, lean_object* v_pre_1937_, lean_object* v_post_1938_, uint8_t v_usedLetOnly_1939_, uint8_t v_skipConstInApp_1940_, uint8_t v_skipInstances_1941_, lean_object* v_body_1942_, lean_object* v_x_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_array_push(v_fvars_1936_, v_x_1943_);
v___x_1952_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1937_, v_post_1938_, v_usedLetOnly_1939_, v_skipConstInApp_1940_, v_skipInstances_1941_, v___x_1951_, v_body_1942_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
return v___x_1952_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1936_ = stack[0].m_obj;
lean_object* v_pre_1937_ = stack[1].m_obj;
lean_object* v_post_1938_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1939_ = stack[3].m_num;
uint8_t v_skipConstInApp_1940_ = stack[4].m_num;
uint8_t v_skipInstances_1941_ = stack[5].m_num;
lean_object* v_body_1942_ = stack[6].m_obj;
lean_object* v_x_1943_ = stack[7].m_obj;
lean_object* v___y_1944_ = stack[8].m_obj;
lean_object* v___y_1945_ = stack[9].m_obj;
lean_object* v___y_1946_ = stack[10].m_obj;
lean_object* v___y_1947_ = stack[11].m_obj;
lean_object* v___y_1948_ = stack[12].m_obj;
lean_object* v___y_1949_ = stack[13].m_obj;
lean_object* v_res_1953_;
v_res_1953_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1936_, v_pre_1937_, v_post_1938_, v_usedLetOnly_1939_, v_skipConstInApp_1940_, v_skipInstances_1941_, v_body_1942_, v_x_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
stack->m_obj
 = v_res_1953_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_1954_, lean_object* v_post_1955_, lean_object* v_usedLetOnly_1956_, lean_object* v_skipConstInApp_1957_, lean_object* v_skipInstances_1958_, lean_object* v_sz_1959_, lean_object* v_i_1960_, lean_object* v_bs_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
uint8_t v_usedLetOnly_boxed_1969_; uint8_t v_skipConstInApp_boxed_1970_; uint8_t v_skipInstances_boxed_1971_; size_t v_sz_boxed_1972_; size_t v_i_boxed_1973_; lean_object* v_res_1974_; 
v_usedLetOnly_boxed_1969_ = lean_unbox(v_usedLetOnly_1956_);
v_skipConstInApp_boxed_1970_ = lean_unbox(v_skipConstInApp_1957_);
v_skipInstances_boxed_1971_ = lean_unbox(v_skipInstances_1958_);
v_sz_boxed_1972_ = lean_unbox_usize(v_sz_1959_);
lean_dec(v_sz_1959_);
v_i_boxed_1973_ = lean_unbox_usize(v_i_1960_);
lean_dec(v_i_1960_);
v_res_1974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1954_, v_post_1955_, v_usedLetOnly_boxed_1969_, v_skipConstInApp_boxed_1970_, v_skipInstances_boxed_1971_, v_sz_boxed_1972_, v_i_boxed_1973_, v_bs_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1962_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1975_, lean_object* v_post_1976_, lean_object* v_usedLetOnly_1977_, lean_object* v_skipConstInApp_1978_, lean_object* v_skipInstances_1979_, lean_object* v_e_1980_, lean_object* v_a_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
uint8_t v_usedLetOnly_boxed_1988_; uint8_t v_skipConstInApp_boxed_1989_; uint8_t v_skipInstances_boxed_1990_; lean_object* v_res_1991_; 
v_usedLetOnly_boxed_1988_ = lean_unbox(v_usedLetOnly_1977_);
v_skipConstInApp_boxed_1989_ = lean_unbox(v_skipConstInApp_1978_);
v_skipInstances_boxed_1990_ = lean_unbox(v_skipInstances_1979_);
v_res_1991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1975_, v_post_1976_, v_usedLetOnly_boxed_1988_, v_skipConstInApp_boxed_1989_, v_skipInstances_boxed_1990_, v_e_1980_, v_a_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v_a_1981_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1992_, lean_object* v_post_1993_, lean_object* v_usedLetOnly_1994_, lean_object* v_skipConstInApp_1995_, lean_object* v_skipInstances_1996_, lean_object* v_fvars_1997_, lean_object* v_e_1998_, lean_object* v_a_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
uint8_t v_usedLetOnly_boxed_2006_; uint8_t v_skipConstInApp_boxed_2007_; uint8_t v_skipInstances_boxed_2008_; lean_object* v_res_2009_; 
v_usedLetOnly_boxed_2006_ = lean_unbox(v_usedLetOnly_1994_);
v_skipConstInApp_boxed_2007_ = lean_unbox(v_skipConstInApp_1995_);
v_skipInstances_boxed_2008_ = lean_unbox(v_skipInstances_1996_);
v_res_2009_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1992_, v_post_1993_, v_usedLetOnly_boxed_2006_, v_skipConstInApp_boxed_2007_, v_skipInstances_boxed_2008_, v_fvars_1997_, v_e_1998_, v_a_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v_a_1999_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_2010_, lean_object* v_post_2011_, lean_object* v_usedLetOnly_2012_, lean_object* v_skipConstInApp_2013_, lean_object* v_skipInstances_2014_, lean_object* v_fvars_2015_, lean_object* v_e_2016_, lean_object* v_a_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v_usedLetOnly_boxed_2024_; uint8_t v_skipConstInApp_boxed_2025_; uint8_t v_skipInstances_boxed_2026_; lean_object* v_res_2027_; 
v_usedLetOnly_boxed_2024_ = lean_unbox(v_usedLetOnly_2012_);
v_skipConstInApp_boxed_2025_ = lean_unbox(v_skipConstInApp_2013_);
v_skipInstances_boxed_2026_ = lean_unbox(v_skipInstances_2014_);
v_res_2027_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_2010_, v_post_2011_, v_usedLetOnly_boxed_2024_, v_skipConstInApp_boxed_2025_, v_skipInstances_boxed_2026_, v_fvars_2015_, v_e_2016_, v_a_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v_a_2017_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_2028_, lean_object* v_post_2029_, lean_object* v_usedLetOnly_2030_, lean_object* v_skipConstInApp_2031_, lean_object* v_skipInstances_2032_, lean_object* v_e_2033_, lean_object* v_a_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v_usedLetOnly_boxed_2041_; uint8_t v_skipConstInApp_boxed_2042_; uint8_t v_skipInstances_boxed_2043_; lean_object* v_res_2044_; 
v_usedLetOnly_boxed_2041_ = lean_unbox(v_usedLetOnly_2030_);
v_skipConstInApp_boxed_2042_ = lean_unbox(v_skipConstInApp_2031_);
v_skipInstances_boxed_2043_ = lean_unbox(v_skipInstances_2032_);
v_res_2044_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2028_, v_post_2029_, v_usedLetOnly_boxed_2041_, v_skipConstInApp_boxed_2042_, v_skipInstances_boxed_2043_, v_e_2033_, v_a_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v_a_2034_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_2045_, lean_object* v_post_2046_, lean_object* v_usedLetOnly_2047_, lean_object* v_skipConstInApp_2048_, lean_object* v_skipInstances_2049_, lean_object* v_fvars_2050_, lean_object* v_e_2051_, lean_object* v_a_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v_usedLetOnly_boxed_2059_; uint8_t v_skipConstInApp_boxed_2060_; uint8_t v_skipInstances_boxed_2061_; lean_object* v_res_2062_; 
v_usedLetOnly_boxed_2059_ = lean_unbox(v_usedLetOnly_2047_);
v_skipConstInApp_boxed_2060_ = lean_unbox(v_skipConstInApp_2048_);
v_skipInstances_boxed_2061_ = lean_unbox(v_skipInstances_2049_);
v_res_2062_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_2045_, v_post_2046_, v_usedLetOnly_boxed_2059_, v_skipConstInApp_boxed_2060_, v_skipInstances_boxed_2061_, v_fvars_2050_, v_e_2051_, v_a_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v_a_2052_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_2063_, lean_object* v___x_2064_, lean_object* v_pre_2065_, lean_object* v_post_2066_, lean_object* v_usedLetOnly_2067_, lean_object* v_skipConstInApp_2068_, lean_object* v_skipInstances_2069_, lean_object* v_a_2070_, lean_object* v_b_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v_usedLetOnly_boxed_2079_; uint8_t v_skipConstInApp_boxed_2080_; uint8_t v_skipInstances_boxed_2081_; lean_object* v_res_2082_; 
v_usedLetOnly_boxed_2079_ = lean_unbox(v_usedLetOnly_2067_);
v_skipConstInApp_boxed_2080_ = lean_unbox(v_skipConstInApp_2068_);
v_skipInstances_boxed_2081_ = lean_unbox(v_skipInstances_2069_);
v_res_2082_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2063_, v___x_2064_, v_pre_2065_, v_post_2066_, v_usedLetOnly_boxed_2079_, v_skipConstInApp_boxed_2080_, v_skipInstances_boxed_2081_, v_a_2070_, v_b_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2072_);
lean_dec_ref(v___x_2064_);
lean_dec(v_upperBound_2063_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2083_, lean_object* v_pre_2084_, lean_object* v_post_2085_, lean_object* v_usedLetOnly_2086_, lean_object* v_skipConstInApp_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_, lean_object* v_x_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
uint8_t v_skipInstances_boxed_2098_; uint8_t v_usedLetOnly_boxed_2099_; uint8_t v_skipConstInApp_boxed_2100_; lean_object* v_res_2101_; 
v_skipInstances_boxed_2098_ = lean_unbox(v_skipInstances_2083_);
v_usedLetOnly_boxed_2099_ = lean_unbox(v_usedLetOnly_2086_);
v_skipConstInApp_boxed_2100_ = lean_unbox(v_skipConstInApp_2087_);
v_res_2101_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2098_, v_pre_2084_, v_post_2085_, v_usedLetOnly_boxed_2099_, v_skipConstInApp_boxed_2100_, v_x_2088_, v_x_2089_, v_x_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2091_);
return v_res_2101_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2102_, lean_object* v_x_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = lean_apply_1(v_x_2103_, lean_box(0));
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v___y_2104_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2103_ = stack[1].m_obj;
lean_object* v___y_2104_ = stack[2].m_obj;
lean_object* v___y_2105_ = stack[3].m_obj;
lean_object* v___y_2106_ = stack[4].m_obj;
lean_object* v___y_2107_ = stack[5].m_obj;
lean_object* v___y_2108_ = stack[6].m_obj;
lean_object* v_res_2113_;
v_res_2113_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v_x_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
stack->m_obj
 = v_res_2113_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_x_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2114_, v_x_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2122_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = lean_box(0);
v___x_2124_ = lean_unsigned_to_nat(16u);
v___x_2125_ = lean_mk_array(v___x_2124_, v___x_2123_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v___x_2126_);
return v___x_2128_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2130_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2130_, 0, lean_box(0));
lean_closure_set(v___x_2130_, 1, lean_box(0));
lean_closure_set(v___x_2130_, 2, v___x_2129_);
return v___x_2130_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2131_, lean_object* v_pre_2132_, lean_object* v_post_2133_, uint8_t v_usedLetOnly_2134_, uint8_t v_skipConstInApp_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v_a_2145_; lean_object* v_fst_2146_; lean_object* v_snd_2147_; lean_object* v___x_2148_; 
v___x_2142_ = 0;
v___x_2143_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2144_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2143_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2144_);
v_fst_2146_ = lean_ctor_get(v_a_2145_, 0);
lean_inc(v_fst_2146_);
v_snd_2147_ = lean_ctor_get(v_a_2145_, 1);
lean_inc(v_snd_2147_);
lean_dec(v_a_2145_);
v___x_2148_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2132_, v_post_2133_, v_usedLetOnly_2134_, v_skipConstInApp_2135_, v___x_2142_, v_input_2131_, v_fst_2146_, v_snd_2147_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v_fst_2150_; lean_object* v_snd_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2170_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2148_, 1);
v_fst_2150_ = lean_ctor_get(v_a_2149_, 0);
lean_inc(v_fst_2150_);
v_snd_2151_ = lean_ctor_get(v_a_2149_, 1);
lean_inc(v_snd_2151_);
lean_dec(v_a_2149_);
v___x_2152_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2152_, 0, lean_box(0));
lean_closure_set(v___x_2152_, 1, lean_box(0));
lean_closure_set(v___x_2152_, 2, v_fst_2146_);
v___x_2153_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2152_, v_snd_2151_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2170_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2170_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v_snd_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2168_; 
v_snd_2158_ = lean_ctor_get(v_a_2154_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_a_2154_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v_a_2154_, 0);
lean_dec(v_unused_2169_);
v___x_2160_ = v_a_2154_;
v_isShared_2161_ = v_isSharedCheck_2168_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_snd_2158_);
lean_dec(v_a_2154_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2168_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v_fst_2150_);
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_fst_2150_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_snd_2158_);
v___x_2163_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2165_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2163_);
v___x_2165_ = v___x_2156_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
else
{
lean_dec(v_fst_2146_);
return v___x_2148_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_2131_ = stack[0].m_obj;
lean_object* v_pre_2132_ = stack[1].m_obj;
lean_object* v_post_2133_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2134_ = stack[3].m_num;
uint8_t v_skipConstInApp_2135_ = stack[4].m_num;
lean_object* v___y_2136_ = stack[5].m_obj;
lean_object* v___y_2137_ = stack[6].m_obj;
lean_object* v___y_2138_ = stack[7].m_obj;
lean_object* v___y_2139_ = stack[8].m_obj;
lean_object* v___y_2140_ = stack[9].m_obj;
lean_object* v_res_2171_;
v_res_2171_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2131_, v_pre_2132_, v_post_2133_, v_usedLetOnly_2134_, v_skipConstInApp_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
stack->m_obj
 = v_res_2171_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2172_, lean_object* v_pre_2173_, lean_object* v_post_2174_, lean_object* v_usedLetOnly_2175_, lean_object* v_skipConstInApp_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
uint8_t v_usedLetOnly_boxed_2183_; uint8_t v_skipConstInApp_boxed_2184_; lean_object* v_res_2185_; 
v_usedLetOnly_boxed_2183_ = lean_unbox(v_usedLetOnly_2175_);
v_skipConstInApp_boxed_2184_ = lean_unbox(v_skipConstInApp_2176_);
v_res_2185_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2172_, v_pre_2173_, v_post_2174_, v_usedLetOnly_boxed_2183_, v_skipConstInApp_boxed_2184_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2185_;
}
}
lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___y_2195_; lean_object* v___x_2212_; uint8_t v_transparency_2213_; lean_object* v___f_2214_; lean_object* v___f_2215_; uint8_t v___x_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2212_ = l_Lean_Meta_Context_config(v_a_2189_);
v_transparency_2213_ = lean_ctor_get_uint8(v___x_2212_, 9);
lean_dec_ref(v___x_2212_);
v___f_2214_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2215_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2216_ = 0;
v___x_2217_ = 3;
v___x_2218_ = lean_box(0);
v___x_2219_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2213_, v___x_2217_);
if (v___x_2219_ == 0)
{
lean_object* v_keyedConfig_2220_; uint8_t v_trackZetaDelta_2221_; lean_object* v_zetaDeltaSet_2222_; lean_object* v_lctx_2223_; lean_object* v_localInstances_2224_; lean_object* v_defEqCtx_x3f_2225_; lean_object* v_synthPendingDepth_2226_; lean_object* v_customCanUnfoldPredicate_x3f_2227_; uint8_t v_univApprox_2228_; uint8_t v_inTypeClassResolution_2229_; uint8_t v_cacheInferType_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v_keyedConfig_2220_ = lean_ctor_get(v_a_2189_, 0);
v_trackZetaDelta_2221_ = lean_ctor_get_uint8(v_a_2189_, sizeof(void*)*7);
v_zetaDeltaSet_2222_ = lean_ctor_get(v_a_2189_, 1);
v_lctx_2223_ = lean_ctor_get(v_a_2189_, 2);
v_localInstances_2224_ = lean_ctor_get(v_a_2189_, 3);
v_defEqCtx_x3f_2225_ = lean_ctor_get(v_a_2189_, 4);
v_synthPendingDepth_2226_ = lean_ctor_get(v_a_2189_, 5);
v_customCanUnfoldPredicate_x3f_2227_ = lean_ctor_get(v_a_2189_, 6);
v_univApprox_2228_ = lean_ctor_get_uint8(v_a_2189_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2229_ = lean_ctor_get_uint8(v_a_2189_, sizeof(void*)*7 + 2);
v_cacheInferType_2230_ = lean_ctor_get_uint8(v_a_2189_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2220_);
v___x_2231_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2217_, v_keyedConfig_2220_);
lean_inc(v_customCanUnfoldPredicate_x3f_2227_);
lean_inc(v_synthPendingDepth_2226_);
lean_inc(v_defEqCtx_x3f_2225_);
lean_inc_ref(v_localInstances_2224_);
lean_inc_ref(v_lctx_2223_);
lean_inc(v_zetaDeltaSet_2222_);
v___x_2232_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v_zetaDeltaSet_2222_);
lean_ctor_set(v___x_2232_, 2, v_lctx_2223_);
lean_ctor_set(v___x_2232_, 3, v_localInstances_2224_);
lean_ctor_set(v___x_2232_, 4, v_defEqCtx_x3f_2225_);
lean_ctor_set(v___x_2232_, 5, v_synthPendingDepth_2226_);
lean_ctor_set(v___x_2232_, 6, v_customCanUnfoldPredicate_x3f_2227_);
lean_ctor_set_uint8(v___x_2232_, sizeof(void*)*7, v_trackZetaDelta_2221_);
lean_ctor_set_uint8(v___x_2232_, sizeof(void*)*7 + 1, v_univApprox_2228_);
lean_ctor_set_uint8(v___x_2232_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2229_);
lean_ctor_set_uint8(v___x_2232_, sizeof(void*)*7 + 3, v_cacheInferType_2230_);
v___x_2233_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2188_, v___f_2215_, v___f_2214_, v___x_2216_, v___x_2216_, v___x_2218_, v___x_2232_, v_a_2190_, v_a_2191_, v_a_2192_);
lean_dec_ref_known(v___x_2232_, 7);
v___y_2195_ = v___x_2233_;
goto v___jp_2194_;
}
else
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2188_, v___f_2215_, v___f_2214_, v___x_2216_, v___x_2216_, v___x_2218_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
v___y_2195_ = v___x_2234_;
goto v___jp_2194_;
}
v___jp_2194_:
{
if (lean_obj_tag(v___y_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_a_2196_ = lean_ctor_get(v___y_2195_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___y_2195_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___y_2195_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___y_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_a_2204_ = lean_ctor_get(v___y_2195_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___y_2195_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___y_2195_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___y_2195_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_expandCoe_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2188_ = stack[0].m_obj;
lean_object* v_a_2189_ = stack[1].m_obj;
lean_object* v_a_2190_ = stack[2].m_obj;
lean_object* v_a_2191_ = stack[3].m_obj;
lean_object* v_a_2192_ = stack[4].m_obj;
lean_object* v_res_2235_;
v_res_2235_ = l_Lean_Meta_expandCoe(v_e_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
stack->m_obj
 = v_res_2235_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Meta_expandCoe(v_e_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2243_, lean_object* v_m_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2244_, v_a_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2247_, lean_object* v_m_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2247_, v_m_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_m_2248_);
return v_res_2250_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_){
_start:
{
uint8_t v___x_2254_; 
v___x_2254_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2252_, v_x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2252_ = stack[1].m_obj;
lean_object* v_x_2253_ = stack[2].m_obj;
uint8_t v_res_2255_;
v_res_2255_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_box(0), v_x_2252_, v_x_2253_);
stack->m_num = v_res_2255_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_){
_start:
{
uint8_t v_res_2259_; lean_object* v_r_2260_; 
v_res_2259_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2256_, v_x_2257_, v_x_2258_);
lean_dec_ref(v_x_2258_);
lean_dec_ref(v_x_2257_);
v_r_2260_ = lean_box(v_res_2259_);
return v_r_2260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2261_, lean_object* v_a_2262_, lean_object* v_x_2263_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2262_, v_x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2265_, lean_object* v_a_2266_, lean_object* v_x_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2265_, v_a_2266_, v_x_2267_);
lean_dec(v_x_2267_);
lean_dec(v_a_2266_);
return v_res_2268_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2269_, lean_object* v___x_2270_, lean_object* v_pre_2271_, lean_object* v_post_2272_, uint8_t v_usedLetOnly_2273_, uint8_t v_skipConstInApp_2274_, uint8_t v_skipInstances_2275_, lean_object* v___x_2276_, lean_object* v_inst_2277_, lean_object* v_R_2278_, lean_object* v_a_2279_, lean_object* v_b_2280_, lean_object* v_c_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2269_, v___x_2270_, v_pre_2271_, v_post_2272_, v_usedLetOnly_2273_, v_skipConstInApp_2274_, v_skipInstances_2275_, v_a_2279_, v_b_2280_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2269_ = stack[0].m_obj;
lean_object* v___x_2270_ = stack[1].m_obj;
lean_object* v_pre_2271_ = stack[2].m_obj;
lean_object* v_post_2272_ = stack[3].m_obj;
uint8_t v_usedLetOnly_2273_ = stack[4].m_num;
uint8_t v_skipConstInApp_2274_ = stack[5].m_num;
uint8_t v_skipInstances_2275_ = stack[6].m_num;
lean_object* v___x_2276_ = stack[7].m_obj;
lean_object* v_a_2279_ = stack[10].m_obj;
lean_object* v_b_2280_ = stack[11].m_obj;
lean_object* v___y_2282_ = stack[13].m_obj;
lean_object* v___y_2283_ = stack[14].m_obj;
lean_object* v___y_2284_ = stack[15].m_obj;
lean_object* v___y_2285_ = stack[16].m_obj;
lean_object* v___y_2286_ = stack[17].m_obj;
lean_object* v___y_2287_ = stack[18].m_obj;
lean_object* v_res_2290_;
v_res_2290_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2269_, v___x_2270_, v_pre_2271_, v_post_2272_, v_usedLetOnly_2273_, v_skipConstInApp_2274_, v_skipInstances_2275_, v___x_2276_, lean_box(0), lean_box(0), v_a_2279_, v_b_2280_, lean_box(0), v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
stack->m_obj
 = v_res_2290_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2291_ = _args[0];
lean_object* v___x_2292_ = _args[1];
lean_object* v_pre_2293_ = _args[2];
lean_object* v_post_2294_ = _args[3];
lean_object* v_usedLetOnly_2295_ = _args[4];
lean_object* v_skipConstInApp_2296_ = _args[5];
lean_object* v_skipInstances_2297_ = _args[6];
lean_object* v___x_2298_ = _args[7];
lean_object* v_inst_2299_ = _args[8];
lean_object* v_R_2300_ = _args[9];
lean_object* v_a_2301_ = _args[10];
lean_object* v_b_2302_ = _args[11];
lean_object* v_c_2303_ = _args[12];
lean_object* v___y_2304_ = _args[13];
lean_object* v___y_2305_ = _args[14];
lean_object* v___y_2306_ = _args[15];
lean_object* v___y_2307_ = _args[16];
lean_object* v___y_2308_ = _args[17];
lean_object* v___y_2309_ = _args[18];
lean_object* v___y_2310_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2311_; uint8_t v_skipConstInApp_boxed_2312_; uint8_t v_skipInstances_boxed_2313_; lean_object* v_res_2314_; 
v_usedLetOnly_boxed_2311_ = lean_unbox(v_usedLetOnly_2295_);
v_skipConstInApp_boxed_2312_ = lean_unbox(v_skipConstInApp_2296_);
v_skipInstances_boxed_2313_ = lean_unbox(v_skipInstances_2297_);
v_res_2314_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2291_, v___x_2292_, v_pre_2293_, v_post_2294_, v_usedLetOnly_boxed_2311_, v_skipConstInApp_boxed_2312_, v_skipInstances_boxed_2313_, v___x_2298_, v_inst_2299_, v_R_2300_, v_a_2301_, v_b_2302_, v_c_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2304_);
lean_dec(v___x_2298_);
lean_dec_ref(v___x_2292_);
lean_dec(v_upperBound_2291_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2315_, lean_object* v_m_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2316_, v_a_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2319_, lean_object* v_m_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2319_, v_m_2320_, v_a_2321_);
lean_dec_ref(v_a_2321_);
lean_dec_ref(v_m_2320_);
return v_res_2322_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2323_, lean_object* v_name_2324_, uint8_t v_bi_2325_, lean_object* v_type_2326_, lean_object* v_k_2327_, uint8_t v_kind_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2324_, v_bi_2325_, v_type_2326_, v_k_2327_, v_kind_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
return v___x_2336_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2324_ = stack[1].m_obj;
uint8_t v_bi_2325_ = stack[2].m_num;
lean_object* v_type_2326_ = stack[3].m_obj;
lean_object* v_k_2327_ = stack[4].m_obj;
uint8_t v_kind_2328_ = stack[5].m_num;
lean_object* v___y_2329_ = stack[6].m_obj;
lean_object* v___y_2330_ = stack[7].m_obj;
lean_object* v___y_2331_ = stack[8].m_obj;
lean_object* v___y_2332_ = stack[9].m_obj;
lean_object* v___y_2333_ = stack[10].m_obj;
lean_object* v___y_2334_ = stack[11].m_obj;
lean_object* v_res_2337_;
v_res_2337_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_box(0), v_name_2324_, v_bi_2325_, v_type_2326_, v_k_2327_, v_kind_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
stack->m_obj
 = v_res_2337_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2338_, lean_object* v_name_2339_, lean_object* v_bi_2340_, lean_object* v_type_2341_, lean_object* v_k_2342_, lean_object* v_kind_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
uint8_t v_bi_boxed_2351_; uint8_t v_kind_boxed_2352_; lean_object* v_res_2353_; 
v_bi_boxed_2351_ = lean_unbox(v_bi_2340_);
v_kind_boxed_2352_ = lean_unbox(v_kind_2343_);
v_res_2353_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2338_, v_name_2339_, v_bi_boxed_2351_, v_type_2341_, v_k_2342_, v_kind_boxed_2352_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2344_);
return v_res_2353_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2354_, lean_object* v_name_2355_, lean_object* v_type_2356_, lean_object* v_val_2357_, lean_object* v_k_2358_, uint8_t v_nondep_2359_, uint8_t v_kind_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2355_, v_type_2356_, v_val_2357_, v_k_2358_, v_nondep_2359_, v_kind_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2355_ = stack[1].m_obj;
lean_object* v_type_2356_ = stack[2].m_obj;
lean_object* v_val_2357_ = stack[3].m_obj;
lean_object* v_k_2358_ = stack[4].m_obj;
uint8_t v_nondep_2359_ = stack[5].m_num;
uint8_t v_kind_2360_ = stack[6].m_num;
lean_object* v___y_2361_ = stack[7].m_obj;
lean_object* v___y_2362_ = stack[8].m_obj;
lean_object* v___y_2363_ = stack[9].m_obj;
lean_object* v___y_2364_ = stack[10].m_obj;
lean_object* v___y_2365_ = stack[11].m_obj;
lean_object* v___y_2366_ = stack[12].m_obj;
lean_object* v_res_2369_;
v_res_2369_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_box(0), v_name_2355_, v_type_2356_, v_val_2357_, v_k_2358_, v_nondep_2359_, v_kind_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
stack->m_obj
 = v_res_2369_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2370_, lean_object* v_name_2371_, lean_object* v_type_2372_, lean_object* v_val_2373_, lean_object* v_k_2374_, lean_object* v_nondep_2375_, lean_object* v_kind_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
uint8_t v_nondep_boxed_2384_; uint8_t v_kind_boxed_2385_; lean_object* v_res_2386_; 
v_nondep_boxed_2384_ = lean_unbox(v_nondep_2375_);
v_kind_boxed_2385_ = lean_unbox(v_kind_2376_);
v_res_2386_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2370_, v_name_2371_, v_type_2372_, v_val_2373_, v_k_2374_, v_nondep_boxed_2384_, v_kind_boxed_2385_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2377_);
return v_res_2386_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2387_, lean_object* v_ref_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2388_);
return v___x_2394_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2388_ = stack[1].m_obj;
lean_object* v___y_2389_ = stack[2].m_obj;
lean_object* v___y_2390_ = stack[3].m_obj;
lean_object* v___y_2391_ = stack[4].m_obj;
lean_object* v___y_2392_ = stack[5].m_obj;
lean_object* v_res_2395_;
v_res_2395_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_box(0), v_ref_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
stack->m_obj
 = v_res_2395_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_ref_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2396_, v_ref_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
return v_res_2403_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2404_, lean_object* v_x_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2405_ = stack[1].m_obj;
lean_object* v___y_2406_ = stack[2].m_obj;
lean_object* v___y_2407_ = stack[3].m_obj;
lean_object* v___y_2408_ = stack[4].m_obj;
lean_object* v___y_2409_ = stack[5].m_obj;
lean_object* v___y_2410_ = stack[6].m_obj;
lean_object* v___y_2411_ = stack[7].m_obj;
lean_object* v_res_2414_;
v_res_2414_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_box(0), v_x_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
stack->m_obj
 = v_res_2414_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2415_, lean_object* v_x_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2415_, v_x_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2417_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2425_, lean_object* v_m_2426_, lean_object* v_a_2427_, lean_object* v_b_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2426_, v_a_2427_, v_b_2428_);
return v___x_2429_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2430_, lean_object* v_x_2431_, size_t v_x_2432_, lean_object* v_x_2433_){
_start:
{
uint8_t v___x_2434_; 
v___x_2434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2431_, v_x_2432_, v_x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2431_ = stack[1].m_obj;
size_t v_x_2432_ = stack[2].m_num;
lean_object* v_x_2433_ = stack[3].m_obj;
uint8_t v_res_2435_;
v_res_2435_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_x_2431_, v_x_2432_, v_x_2433_);
stack->m_num = v_res_2435_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2436_, lean_object* v_x_2437_, lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
size_t v_x_40936__boxed_2440_; uint8_t v_res_2441_; lean_object* v_r_2442_; 
v_x_40936__boxed_2440_ = lean_unbox_usize(v_x_2438_);
lean_dec(v_x_2438_);
v_res_2441_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2436_, v_x_2437_, v_x_40936__boxed_2440_, v_x_2439_);
lean_dec_ref(v_x_2439_);
lean_dec_ref(v_x_2437_);
v_r_2442_ = lean_box(v_res_2441_);
return v_r_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object* v_00_u03b2_2443_, lean_object* v_a_2444_, lean_object* v_x_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_2444_, v_x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object* v_00_u03b2_2447_, lean_object* v_a_2448_, lean_object* v_x_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_2447_, v_a_2448_, v_x_2449_);
lean_dec(v_x_2449_);
lean_dec_ref(v_a_2448_);
return v_res_2450_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2451_, lean_object* v_a_2452_, lean_object* v_x_2453_){
_start:
{
uint8_t v___x_2454_; 
v___x_2454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2452_, v_x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2452_ = stack[1].m_obj;
lean_object* v_x_2453_ = stack[2].m_obj;
uint8_t v_res_2455_;
v_res_2455_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_box(0), v_a_2452_, v_x_2453_);
stack->m_num = v_res_2455_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2456_, lean_object* v_a_2457_, lean_object* v_x_2458_){
_start:
{
uint8_t v_res_2459_; lean_object* v_r_2460_; 
v_res_2459_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2456_, v_a_2457_, v_x_2458_);
lean_dec(v_x_2458_);
lean_dec_ref(v_a_2457_);
v_r_2460_ = lean_box(v_res_2459_);
return v_r_2460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2461_, lean_object* v_data_2462_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2464_, lean_object* v_a_2465_, lean_object* v_b_2466_, lean_object* v_x_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2465_, v_b_2466_, v_x_2467_);
return v___x_2468_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2469_, lean_object* v_keys_2470_, lean_object* v_vals_2471_, lean_object* v_heq_2472_, lean_object* v_i_2473_, lean_object* v_k_2474_){
_start:
{
uint8_t v___x_2475_; 
v___x_2475_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2470_, v_i_2473_, v_k_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2470_ = stack[1].m_obj;
lean_object* v_vals_2471_ = stack[2].m_obj;
lean_object* v_i_2473_ = stack[4].m_obj;
lean_object* v_k_2474_ = stack[5].m_obj;
uint8_t v_res_2476_;
v_res_2476_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_box(0), v_keys_2470_, v_vals_2471_, lean_box(0), v_i_2473_, v_k_2474_);
stack->m_num = v_res_2476_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2477_, lean_object* v_keys_2478_, lean_object* v_vals_2479_, lean_object* v_heq_2480_, lean_object* v_i_2481_, lean_object* v_k_2482_){
_start:
{
uint8_t v_res_2483_; lean_object* v_r_2484_; 
v_res_2483_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2477_, v_keys_2478_, v_vals_2479_, v_heq_2480_, v_i_2481_, v_k_2482_);
lean_dec_ref(v_k_2482_);
lean_dec_ref(v_vals_2479_);
lean_dec_ref(v_keys_2478_);
v_r_2484_ = lean_box(v_res_2483_);
return v_r_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2485_, lean_object* v_i_2486_, lean_object* v_source_2487_, lean_object* v_target_2488_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2486_, v_source_2487_, v_target_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2490_, lean_object* v_x_2491_, lean_object* v_x_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2491_, v_x_2492_);
return v___x_2493_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2494_, lean_object* v_decl_2495_, lean_object* v_ref_2496_){
_start:
{
lean_object* v_defValue_2498_; lean_object* v_descr_2499_; lean_object* v_deprecation_x3f_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_defValue_2498_ = lean_ctor_get(v_decl_2495_, 0);
v_descr_2499_ = lean_ctor_get(v_decl_2495_, 1);
v_deprecation_x3f_2500_ = lean_ctor_get(v_decl_2495_, 2);
v___x_2501_ = lean_alloc_ctor(1, 0, 1);
v___x_2502_ = lean_unbox(v_defValue_2498_);
lean_ctor_set_uint8(v___x_2501_, 0, v___x_2502_);
lean_inc(v_deprecation_x3f_2500_);
lean_inc_ref(v_descr_2499_);
lean_inc_n(v_name_2494_, 2);
v___x_2503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2503_, 0, v_name_2494_);
lean_ctor_set(v___x_2503_, 1, v_ref_2496_);
lean_ctor_set(v___x_2503_, 2, v___x_2501_);
lean_ctor_set(v___x_2503_, 3, v_descr_2499_);
lean_ctor_set(v___x_2503_, 4, v_deprecation_x3f_2500_);
v___x_2504_ = lean_register_option(v_name_2494_, v___x_2503_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2512_; 
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2504_, 0);
lean_dec(v_unused_2513_);
v___x_2506_ = v___x_2504_;
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
else
{
lean_dec(v___x_2504_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
lean_inc(v_defValue_2498_);
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_name_2494_);
lean_ctor_set(v___x_2508_, 1, v_defValue_2498_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_name_2494_);
v_a_2514_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2504_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2504_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2494_ = stack[0].m_obj;
lean_object* v_decl_2495_ = stack[1].m_obj;
lean_object* v_ref_2496_ = stack[2].m_obj;
lean_object* v_res_2522_;
v_res_2522_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2494_, v_decl_2495_, v_ref_2496_);
stack->m_obj
 = v_res_2522_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2523_, lean_object* v_decl_2524_, lean_object* v_ref_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2523_, v_decl_2524_, v_ref_2525_);
lean_dec_ref(v_decl_2524_);
return v_res_2527_;
}
}
lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2542_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2543_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2544_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2545_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2542_, v___x_2543_, v___x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2546_;
v_res_2546_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
stack->m_obj
 = v_res_2546_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2548_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_ref_2555_; lean_object* v___x_2556_; lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2565_; 
v_ref_2555_ = lean_ctor_get(v___y_2552_, 2);
v___x_2556_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
lean_inc(v_ref_2555_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_ref_2555_);
lean_ctor_set(v___x_2561_, 1, v_a_2557_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set_tag(v___x_2559_, 1);
lean_ctor_set(v___x_2559_, 0, v___x_2561_);
v___x_2563_ = v___x_2559_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2549_ = stack[0].m_obj;
lean_object* v___y_2550_ = stack[1].m_obj;
lean_object* v___y_2551_ = stack[2].m_obj;
lean_object* v___y_2552_ = stack[3].m_obj;
lean_object* v___y_2553_ = stack[4].m_obj;
lean_object* v_res_2566_;
v_res_2566_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
stack->m_obj
 = v_res_2566_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
return v_res_2573_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2582_ = l_Lean_stringToMessageData(v___x_2581_);
return v___x_2582_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2585_ = l_Lean_stringToMessageData(v___x_2584_);
return v___x_2585_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2588_ = l_Lean_stringToMessageData(v___x_2587_);
return v___x_2588_;
}
}
lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2589_, lean_object* v_expectedType_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v___x_2596_; 
lean_inc(v_a_2594_);
lean_inc_ref(v_a_2593_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc_ref(v_expr_2589_);
v___x_2596_ = lean_infer_type(v_expr_2589_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2598_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc_n(v_a_2597_, 2);
lean_dec_ref_known(v___x_2596_, 1);
v___x_2598_ = l_Lean_Meta_getLevel(v_a_2597_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2600_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
lean_inc_ref(v_expectedType_2590_);
v___x_2600_ = l_Lean_Meta_getLevel(v_expectedType_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v___x_2602_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2604_, 0, v_a_2601_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2605_, 0, v_a_2599_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
lean_inc_ref(v___x_2605_);
v___x_2606_ = l_Lean_mkConst(v___x_2602_, v___x_2605_);
v___x_2607_ = lean_unsigned_to_nat(3u);
v___x_2608_ = lean_mk_empty_array_with_capacity(v___x_2607_);
lean_inc(v_a_2597_);
v___x_2609_ = lean_array_push(v___x_2608_, v_a_2597_);
lean_inc_ref(v_expr_2589_);
v___x_2610_ = lean_array_push(v___x_2609_, v_expr_2589_);
lean_inc_ref(v_expectedType_2590_);
v___x_2611_ = lean_array_push(v___x_2610_, v_expectedType_2590_);
v___x_2612_ = l_Lean_mkAppN(v___x_2606_, v___x_2611_);
lean_dec_ref(v___x_2611_);
v___x_2613_ = lean_box(0);
v___x_2614_ = l_Lean_Meta_trySynthInstance(v___x_2612_, v___x_2613_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2712_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2712_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2712_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
switch(lean_obj_tag(v_a_2615_))
{
case 0:
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
lean_dec_ref_known(v___x_2605_, 2);
lean_dec(v_a_2597_);
lean_dec_ref(v_expectedType_2590_);
lean_dec_ref(v_expr_2589_);
v___x_2619_ = lean_box(0);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
case 1:
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2707_; 
lean_del_object(v___x_2617_);
v_a_2623_ = lean_ctor_get(v_a_2615_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_a_2615_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2625_ = v_a_2615_;
v_isShared_2626_ = v_isSharedCheck_2707_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v_a_2615_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2707_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2627_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2628_ = l_Lean_mkConst(v___x_2627_, v___x_2605_);
v___x_2629_ = lean_unsigned_to_nat(4u);
v___x_2630_ = lean_mk_empty_array_with_capacity(v___x_2629_);
v___x_2631_ = lean_array_push(v___x_2630_, v_a_2597_);
lean_inc_ref(v_expr_2589_);
v___x_2632_ = lean_array_push(v___x_2631_, v_expr_2589_);
lean_inc_ref(v_expectedType_2590_);
v___x_2633_ = lean_array_push(v___x_2632_, v_expectedType_2590_);
v___x_2634_ = lean_array_push(v___x_2633_, v_a_2623_);
v___x_2635_ = l_Lean_mkAppN(v___x_2628_, v___x_2634_);
lean_dec_ref(v___x_2634_);
v___x_2636_ = l_Lean_Meta_expandCoe(v___x_2635_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2698_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2698_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2698_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_fst_2648_; lean_object* v___x_2649_; 
v_fst_2648_ = lean_ctor_get(v_a_2637_, 0);
lean_inc(v_a_2594_);
lean_inc_ref(v_a_2593_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_fst_2648_);
v___x_2649_ = lean_infer_type(v_fst_2648_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
lean_inc_ref(v_expectedType_2590_);
v___x_2651_ = l_Lean_Meta_isExprDefEq(v_a_2650_, v_expectedType_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; uint8_t v___x_2653_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v___x_2653_ = lean_unbox(v_a_2652_);
lean_dec(v_a_2652_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2679_; 
lean_inc(v_fst_2648_);
lean_del_object(v___x_2639_);
lean_del_object(v___x_2625_);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_a_2637_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; lean_object* v_unused_2681_; 
v_unused_2680_ = lean_ctor_get(v_a_2637_, 1);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_a_2637_, 0);
lean_dec(v_unused_2681_);
v___x_2655_ = v_a_2637_;
v_isShared_2656_ = v_isSharedCheck_2679_;
goto v_resetjp_2654_;
}
else
{
lean_dec(v_a_2637_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2679_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2657_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2658_ = l_Lean_indentExpr(v_expr_2589_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 7);
lean_ctor_set(v___x_2655_, 1, v___x_2658_);
lean_ctor_set(v___x_2655_, 0, v___x_2657_);
v___x_2660_ = v___x_2655_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v___x_2661_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2660_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v___x_2663_ = l_Lean_indentExpr(v_expectedType_2590_);
v___x_2664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2662_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
v___x_2665_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Lean_indentExpr(v_fst_2648_);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2668_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2590_);
lean_dec_ref(v_expr_2589_);
goto v___jp_2641_;
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_del_object(v___x_2639_);
lean_dec(v_a_2637_);
lean_del_object(v___x_2625_);
lean_dec_ref(v_expectedType_2590_);
lean_dec_ref(v_expr_2589_);
v_a_2682_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2651_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2651_);
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
lean_del_object(v___x_2639_);
lean_dec(v_a_2637_);
lean_del_object(v___x_2625_);
lean_dec_ref(v_expectedType_2590_);
lean_dec_ref(v_expr_2589_);
v_a_2690_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2649_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2649_);
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
v___jp_2641_:
{
lean_object* v___x_2643_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v_a_2637_);
v___x_2643_ = v___x_2625_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2637_);
v___x_2643_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2645_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2643_);
v___x_2645_ = v___x_2639_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_del_object(v___x_2625_);
lean_dec_ref(v_expectedType_2590_);
lean_dec_ref(v_expr_2589_);
v_a_2699_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2636_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2636_);
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
default: 
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
lean_dec_ref_known(v___x_2605_, 2);
lean_dec(v_a_2597_);
lean_dec_ref(v_expectedType_2590_);
lean_dec_ref(v_expr_2589_);
v___x_2708_ = lean_box(2);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2708_);
v___x_2710_ = v___x_2617_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref_known(v___x_2605_, 2);
lean_dec(v_a_2597_);
lean_dec_ref(v_expectedType_2590_);
lean_dec_ref(v_expr_2589_);
v_a_2713_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2614_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2614_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec(v_a_2599_);
lean_dec(v_a_2597_);
lean_dec_ref(v_expectedType_2590_);
lean_dec_ref(v_expr_2589_);
v_a_2721_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2600_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2600_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec(v_a_2597_);
lean_dec_ref(v_expectedType_2590_);
lean_dec_ref(v_expr_2589_);
v_a_2729_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2598_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2598_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v_expectedType_2590_);
lean_dec_ref(v_expr_2589_);
v_a_2737_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2596_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2596_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_coerceSimpleRecordingNames_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_2589_ = stack[0].m_obj;
lean_object* v_expectedType_2590_ = stack[1].m_obj;
lean_object* v_a_2591_ = stack[2].m_obj;
lean_object* v_a_2592_ = stack[3].m_obj;
lean_object* v_a_2593_ = stack[4].m_obj;
lean_object* v_a_2594_ = stack[5].m_obj;
lean_object* v_res_2745_;
v_res_2745_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2589_, v_expectedType_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
stack->m_obj
 = v_res_2745_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2746_, lean_object* v_expectedType_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2746_, v_expectedType_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
return v_res_2753_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2754_, lean_object* v_msg_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2761_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2755_ = stack[1].m_obj;
lean_object* v___y_2756_ = stack[2].m_obj;
lean_object* v___y_2757_ = stack[3].m_obj;
lean_object* v___y_2758_ = stack[4].m_obj;
lean_object* v___y_2759_ = stack[5].m_obj;
lean_object* v_res_2762_;
v_res_2762_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_box(0), v_msg_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
stack->m_obj
 = v_res_2762_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2763_, lean_object* v_msg_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2763_, v_msg_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
return v_res_2770_;
}
}
lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2771_, lean_object* v_expectedType_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2771_, v_expectedType_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2803_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2803_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2803_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
switch(lean_obj_tag(v_a_2779_))
{
case 0:
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2783_ = lean_box(0);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2783_);
v___x_2785_ = v___x_2781_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
case 1:
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2798_; 
v_a_2787_ = lean_ctor_get(v_a_2779_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_a_2779_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2789_ = v_a_2779_;
v_isShared_2790_ = v_isSharedCheck_2798_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v_a_2779_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2798_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v_fst_2791_; lean_object* v___x_2793_; 
v_fst_2791_ = lean_ctor_get(v_a_2787_, 0);
lean_inc(v_fst_2791_);
lean_dec(v_a_2787_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 0, v_fst_2791_);
v___x_2793_ = v___x_2789_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_fst_2791_);
v___x_2793_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2795_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2793_);
v___x_2795_ = v___x_2781_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
default: 
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2799_ = lean_box(2);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2799_);
v___x_2801_ = v___x_2781_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_a_2804_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2778_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2778_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_coerceSimple_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_2771_ = stack[0].m_obj;
lean_object* v_expectedType_2772_ = stack[1].m_obj;
lean_object* v_a_2773_ = stack[2].m_obj;
lean_object* v_a_2774_ = stack[3].m_obj;
lean_object* v_a_2775_ = stack[4].m_obj;
lean_object* v_a_2776_ = stack[5].m_obj;
lean_object* v_res_2812_;
v_res_2812_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2771_, v_expectedType_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
stack->m_obj
 = v_res_2812_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2813_, lean_object* v_expectedType_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2813_, v_expectedType_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
return v_res_2820_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2829_ = l_Lean_stringToMessageData(v___x_2828_);
return v___x_2829_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2832_ = l_Lean_stringToMessageData(v___x_2831_);
return v___x_2832_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2835_ = l_Lean_stringToMessageData(v___x_2834_);
return v___x_2835_;
}
}
lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2842_; 
lean_inc(v_a_2840_);
lean_inc_ref(v_a_2839_);
lean_inc(v_a_2838_);
lean_inc_ref(v_a_2837_);
lean_inc_ref(v_expr_2836_);
v___x_2842_ = lean_infer_type(v_expr_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc_n(v_a_2843_, 2);
lean_dec_ref_known(v___x_2842_, 1);
v___x_2844_ = l_Lean_Meta_getLevel(v_a_2843_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc_n(v_a_2847_, 2);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = l_Lean_mkSort(v_a_2847_);
lean_inc(v_a_2843_);
v___x_2849_ = l_Lean_mkArrow(v_a_2843_, v___x_2848_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v_a_2850_);
v___x_2852_ = 0;
v___x_2853_ = lean_box(0);
v___x_2854_ = l_Lean_Meta_mkFreshExprMVar(v___x_2851_, v___x_2852_, v___x_2853_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc_n(v_a_2855_, 2);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2857_ = lean_box(0);
v___x_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2858_, 0, v_a_2847_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2859_, 0, v_a_2845_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
lean_inc_ref(v___x_2859_);
v___x_2860_ = l_Lean_Expr_const___override(v___x_2856_, v___x_2859_);
lean_inc(v_a_2843_);
v___x_2861_ = l_Lean_mkAppB(v___x_2860_, v_a_2843_, v_a_2855_);
v___x_2862_ = lean_box(0);
v___x_2863_ = l_Lean_Meta_trySynthInstance(v___x_2861_, v___x_2862_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2950_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2950_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2950_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
if (lean_obj_tag(v_a_2864_) == 1)
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2946_; 
lean_del_object(v___x_2866_);
v_a_2868_ = lean_ctor_get(v_a_2864_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_a_2864_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2870_ = v_a_2864_;
v_isShared_2871_ = v_isSharedCheck_2946_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v_a_2864_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2946_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2872_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2873_ = l_Lean_Expr_const___override(v___x_2872_, v___x_2859_);
lean_inc_ref(v_expr_2836_);
lean_inc(v_a_2868_);
v___x_2874_ = l_Lean_mkApp4(v___x_2873_, v_a_2843_, v_a_2855_, v_a_2868_, v_expr_2836_);
v___x_2875_ = l_Lean_Meta_expandCoe(v___x_2874_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2937_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2937_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2937_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_fst_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2935_; 
v_fst_2880_ = lean_ctor_get(v_a_2876_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_a_2876_);
if (v_isSharedCheck_2935_ == 0)
{
lean_object* v_unused_2936_; 
v_unused_2936_ = lean_ctor_get(v_a_2876_, 1);
lean_dec(v_unused_2936_);
v___x_2882_ = v_a_2876_;
v_isShared_2883_ = v_isSharedCheck_2935_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_fst_2880_);
lean_dec(v_a_2876_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2935_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2891_; 
lean_inc(v_a_2840_);
lean_inc_ref(v_a_2839_);
lean_inc(v_a_2838_);
lean_inc_ref(v_a_2837_);
lean_inc(v_fst_2880_);
v___x_2891_ = lean_infer_type(v_fst_2880_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
lean_inc(v_a_2840_);
lean_inc_ref(v_a_2839_);
lean_inc(v_a_2838_);
lean_inc_ref(v_a_2837_);
v___x_2893_ = lean_whnf(v_a_2892_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; uint8_t v___x_2895_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = l_Lean_Expr_isForall(v_a_2894_);
lean_dec(v_a_2894_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
lean_del_object(v___x_2878_);
lean_del_object(v___x_2870_);
v___x_2896_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2897_ = l_Lean_indentExpr(v_expr_2836_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set_tag(v___x_2882_, 7);
lean_ctor_set(v___x_2882_, 1, v___x_2897_);
lean_ctor_set(v___x_2882_, 0, v___x_2896_);
v___x_2899_ = v___x_2882_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
v___x_2900_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = l_Lean_indentExpr(v_fst_2880_);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2905_ = l_Lean_indentExpr(v_a_2868_);
v___x_2906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = l_Lean_MessageData_hint_x27(v___x_2906_);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2903_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2908_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
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
lean_del_object(v___x_2882_);
lean_dec(v_a_2868_);
lean_dec_ref(v_expr_2836_);
goto v___jp_2884_;
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_del_object(v___x_2882_);
lean_dec(v_fst_2880_);
lean_del_object(v___x_2878_);
lean_del_object(v___x_2870_);
lean_dec(v_a_2868_);
lean_dec_ref(v_expr_2836_);
v_a_2919_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2893_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2893_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_del_object(v___x_2882_);
lean_dec(v_fst_2880_);
lean_del_object(v___x_2878_);
lean_del_object(v___x_2870_);
lean_dec(v_a_2868_);
lean_dec_ref(v_expr_2836_);
v_a_2927_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2891_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2891_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
v___jp_2884_:
{
lean_object* v___x_2886_; 
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v_fst_2880_);
v___x_2886_ = v___x_2870_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_fst_2880_);
v___x_2886_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2886_);
v___x_2888_ = v___x_2878_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_del_object(v___x_2870_);
lean_dec(v_a_2868_);
lean_dec_ref(v_expr_2836_);
v_a_2938_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2875_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2875_);
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
}
else
{
lean_object* v___x_2948_; 
lean_dec(v_a_2864_);
lean_dec_ref_known(v___x_2859_, 2);
lean_dec(v_a_2855_);
lean_dec(v_a_2843_);
lean_dec_ref(v_expr_2836_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2862_);
v___x_2948_ = v___x_2866_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2862_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec_ref_known(v___x_2859_, 2);
lean_dec(v_a_2855_);
lean_dec(v_a_2843_);
lean_dec_ref(v_expr_2836_);
v_a_2951_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2863_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2863_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec(v_a_2847_);
lean_dec(v_a_2845_);
lean_dec(v_a_2843_);
lean_dec_ref(v_expr_2836_);
v_a_2959_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2854_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2854_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
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
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_a_2847_);
lean_dec(v_a_2845_);
lean_dec(v_a_2843_);
lean_dec_ref(v_expr_2836_);
v_a_2967_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2849_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2849_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_a_2845_);
lean_dec(v_a_2843_);
lean_dec_ref(v_expr_2836_);
v_a_2975_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2846_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2846_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v_a_2843_);
lean_dec_ref(v_expr_2836_);
v_a_2983_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2844_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2844_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v_expr_2836_);
v_a_2991_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2842_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2842_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_coerceToFunction_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_2836_ = stack[0].m_obj;
lean_object* v_a_2837_ = stack[1].m_obj;
lean_object* v_a_2838_ = stack[2].m_obj;
lean_object* v_a_2839_ = stack[3].m_obj;
lean_object* v_a_2840_ = stack[4].m_obj;
lean_object* v_res_2999_;
v_res_2999_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
stack->m_obj
 = v_res_2999_;
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
lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
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
LEAN_EXPORT void l_Lean_Meta_coerceToSort_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_3019_ = stack[0].m_obj;
lean_object* v_a_3020_ = stack[1].m_obj;
lean_object* v_a_3021_ = stack[2].m_obj;
lean_object* v_a_3022_ = stack[3].m_obj;
lean_object* v_a_3023_ = stack[4].m_obj;
lean_object* v_res_3172_;
v_res_3172_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
stack->m_obj
 = v_res_3172_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
return v_res_3179_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3180_, lean_object* v___y_3181_){
_start:
{
uint8_t v___x_3183_; 
v___x_3183_ = l_Lean_Expr_hasMVar(v_e_3180_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v_e_3180_);
return v___x_3184_;
}
else
{
lean_object* v___x_3185_; lean_object* v_mctx_3186_; lean_object* v___x_3187_; lean_object* v_fst_3188_; lean_object* v_snd_3189_; lean_object* v___x_3190_; lean_object* v_cache_3191_; lean_object* v_zetaDeltaFVarIds_3192_; lean_object* v_postponed_3193_; lean_object* v_diag_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3203_; 
v___x_3185_ = lean_st_ref_get(v___y_3181_);
v_mctx_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc_ref(v_mctx_3186_);
lean_dec(v___x_3185_);
v___x_3187_ = l_Lean_instantiateMVarsCore(v_mctx_3186_, v_e_3180_);
v_fst_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_fst_3188_);
v_snd_3189_ = lean_ctor_get(v___x_3187_, 1);
lean_inc(v_snd_3189_);
lean_dec_ref(v___x_3187_);
v___x_3190_ = lean_st_ref_take(v___y_3181_);
v_cache_3191_ = lean_ctor_get(v___x_3190_, 1);
v_zetaDeltaFVarIds_3192_ = lean_ctor_get(v___x_3190_, 2);
v_postponed_3193_ = lean_ctor_get(v___x_3190_, 3);
v_diag_3194_ = lean_ctor_get(v___x_3190_, 4);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3203_ == 0)
{
lean_object* v_unused_3204_; 
v_unused_3204_ = lean_ctor_get(v___x_3190_, 0);
lean_dec(v_unused_3204_);
v___x_3196_ = v___x_3190_;
v_isShared_3197_ = v_isSharedCheck_3203_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_diag_3194_);
lean_inc(v_postponed_3193_);
lean_inc(v_zetaDeltaFVarIds_3192_);
lean_inc(v_cache_3191_);
lean_dec(v___x_3190_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3203_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v_snd_3189_);
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_snd_3189_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v_cache_3191_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v_zetaDeltaFVarIds_3192_);
lean_ctor_set(v_reuseFailAlloc_3202_, 3, v_postponed_3193_);
lean_ctor_set(v_reuseFailAlloc_3202_, 4, v_diag_3194_);
v___x_3199_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_st_ref_put(v___y_3181_, v___x_3199_);
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v_fst_3188_);
return v___x_3201_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3180_ = stack[0].m_obj;
lean_object* v___y_3181_ = stack[1].m_obj;
lean_object* v_res_3205_;
v_res_3205_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3180_, v___y_3181_);
stack->m_obj
 = v_res_3205_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3206_, v___y_3207_);
lean_dec(v___y_3207_);
return v_res_3209_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3210_, v___y_3212_);
return v___x_3216_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3210_ = stack[0].m_obj;
lean_object* v___y_3211_ = stack[1].m_obj;
lean_object* v___y_3212_ = stack[2].m_obj;
lean_object* v___y_3213_ = stack[3].m_obj;
lean_object* v___y_3214_ = stack[4].m_obj;
lean_object* v_res_3217_;
v_res_3217_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
stack->m_obj
 = v_res_3217_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
return v_res_3224_;
}
}
lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v___y_3232_; lean_object* v___x_3271_; uint8_t v_transparency_3272_; uint8_t v___x_3273_; uint8_t v___x_3274_; 
v___x_3271_ = l_Lean_Meta_Context_config(v_a_3226_);
v_transparency_3272_ = lean_ctor_get_uint8(v___x_3271_, 9);
lean_dec_ref(v___x_3271_);
v___x_3273_ = 2;
v___x_3274_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3272_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_object* v_keyedConfig_3275_; uint8_t v_trackZetaDelta_3276_; lean_object* v_zetaDeltaSet_3277_; lean_object* v_lctx_3278_; lean_object* v_localInstances_3279_; lean_object* v_defEqCtx_x3f_3280_; lean_object* v_synthPendingDepth_3281_; lean_object* v_customCanUnfoldPredicate_x3f_3282_; uint8_t v_univApprox_3283_; uint8_t v_inTypeClassResolution_3284_; uint8_t v_cacheInferType_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_keyedConfig_3275_ = lean_ctor_get(v_a_3226_, 0);
v_trackZetaDelta_3276_ = lean_ctor_get_uint8(v_a_3226_, sizeof(void*)*7);
v_zetaDeltaSet_3277_ = lean_ctor_get(v_a_3226_, 1);
v_lctx_3278_ = lean_ctor_get(v_a_3226_, 2);
v_localInstances_3279_ = lean_ctor_get(v_a_3226_, 3);
v_defEqCtx_x3f_3280_ = lean_ctor_get(v_a_3226_, 4);
v_synthPendingDepth_3281_ = lean_ctor_get(v_a_3226_, 5);
v_customCanUnfoldPredicate_x3f_3282_ = lean_ctor_get(v_a_3226_, 6);
v_univApprox_3283_ = lean_ctor_get_uint8(v_a_3226_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3284_ = lean_ctor_get_uint8(v_a_3226_, sizeof(void*)*7 + 2);
v_cacheInferType_3285_ = lean_ctor_get_uint8(v_a_3226_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3275_);
v___x_3286_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3273_, v_keyedConfig_3275_);
lean_inc(v_customCanUnfoldPredicate_x3f_3282_);
lean_inc(v_synthPendingDepth_3281_);
lean_inc(v_defEqCtx_x3f_3280_);
lean_inc_ref(v_localInstances_3279_);
lean_inc_ref(v_lctx_3278_);
lean_inc(v_zetaDeltaSet_3277_);
v___x_3287_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
lean_ctor_set(v___x_3287_, 1, v_zetaDeltaSet_3277_);
lean_ctor_set(v___x_3287_, 2, v_lctx_3278_);
lean_ctor_set(v___x_3287_, 3, v_localInstances_3279_);
lean_ctor_set(v___x_3287_, 4, v_defEqCtx_x3f_3280_);
lean_ctor_set(v___x_3287_, 5, v_synthPendingDepth_3281_);
lean_ctor_set(v___x_3287_, 6, v_customCanUnfoldPredicate_x3f_3282_);
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*7, v_trackZetaDelta_3276_);
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*7 + 1, v_univApprox_3283_);
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3284_);
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*7 + 3, v_cacheInferType_3285_);
lean_inc(v_a_3229_);
lean_inc_ref(v_a_3228_);
lean_inc(v_a_3227_);
v___x_3288_ = lean_whnf(v_type_3225_, v___x_3287_, v_a_3227_, v_a_3228_, v_a_3229_);
v___y_3232_ = v___x_3288_;
goto v___jp_3231_;
}
else
{
lean_object* v___x_3289_; 
lean_inc(v_a_3229_);
lean_inc_ref(v_a_3228_);
lean_inc(v_a_3227_);
lean_inc_ref(v_a_3226_);
v___x_3289_ = lean_whnf(v_type_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
v___y_3232_ = v___x_3289_;
goto v___jp_3231_;
}
v___jp_3231_:
{
if (lean_obj_tag(v___y_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3262_; 
v_a_3233_ = lean_ctor_get(v___y_3232_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___y_3232_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3235_ = v___y_3232_;
v_isShared_3236_ = v_isSharedCheck_3262_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___y_3232_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3262_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
if (lean_obj_tag(v_a_3233_) == 5)
{
lean_object* v_fn_3237_; lean_object* v_arg_3238_; lean_object* v___x_3239_; lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3257_; 
lean_del_object(v___x_3235_);
v_fn_3237_ = lean_ctor_get(v_a_3233_, 0);
lean_inc_ref(v_fn_3237_);
v_arg_3238_ = lean_ctor_get(v_a_3233_, 1);
lean_inc_ref(v_arg_3238_);
lean_dec_ref_known(v_a_3233_, 2);
v___x_3239_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3237_, v_a_3227_);
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3257_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3257_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3256_; 
v___x_3244_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3238_, v_a_3227_);
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3256_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3256_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v_a_3240_);
lean_ctor_set(v___x_3249_, 1, v_a_3245_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 1);
lean_ctor_set(v___x_3242_, 0, v___x_3249_);
v___x_3251_ = v___x_3242_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
lean_object* v___x_3253_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v___x_3251_);
v___x_3253_ = v___x_3247_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
lean_dec(v_a_3233_);
v___x_3258_ = lean_box(0);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3258_);
v___x_3260_ = v___x_3235_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
v_a_3263_ = lean_ctor_get(v___y_3232_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___y_3232_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___y_3232_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___y_3232_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isTypeApp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_3225_ = stack[0].m_obj;
lean_object* v_a_3226_ = stack[1].m_obj;
lean_object* v_a_3227_ = stack[2].m_obj;
lean_object* v_a_3228_ = stack[3].m_obj;
lean_object* v_a_3229_ = stack[4].m_obj;
lean_object* v_res_3290_;
v_res_3290_ = l_Lean_Meta_isTypeApp_x3f(v_type_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
stack->m_obj
 = v_res_3290_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_Meta_isTypeApp_x3f(v_type_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
return v_res_3297_;
}
}
lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Lean_Meta_isTypeApp_x3f(v_type_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3340_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3307_ = v___x_3304_;
v_isShared_3308_ = v_isSharedCheck_3340_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3304_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3340_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
if (lean_obj_tag(v_a_3305_) == 1)
{
lean_object* v_val_3309_; lean_object* v_fst_3310_; lean_object* v___x_3311_; 
lean_del_object(v___x_3307_);
v_val_3309_ = lean_ctor_get(v_a_3305_, 0);
lean_inc(v_val_3309_);
lean_dec_ref_known(v_a_3305_, 1);
v_fst_3310_ = lean_ctor_get(v_val_3309_, 0);
lean_inc(v_fst_3310_);
lean_dec(v_val_3309_);
v___x_3311_ = l_Lean_Meta_isMonad_x3f(v_fst_3310_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3326_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3326_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3326_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
if (lean_obj_tag(v_a_3312_) == 0)
{
uint8_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3316_ = 0;
v___x_3317_ = lean_box(v___x_3316_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3317_);
v___x_3319_ = v___x_3314_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
else
{
uint8_t v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
lean_dec_ref_known(v_a_3312_, 1);
v___x_3321_ = 1;
v___x_3322_ = lean_box(v___x_3321_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3322_);
v___x_3324_ = v___x_3314_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
v_a_3327_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3311_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3311_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
else
{
uint8_t v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3338_; 
lean_dec(v_a_3305_);
v___x_3335_ = 0;
v___x_3336_ = lean_box(v___x_3335_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v___x_3336_);
v___x_3338_ = v___x_3307_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
v_a_3341_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3304_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3304_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isMonadApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_3298_ = stack[0].m_obj;
lean_object* v_a_3299_ = stack[1].m_obj;
lean_object* v_a_3300_ = stack[2].m_obj;
lean_object* v_a_3301_ = stack[3].m_obj;
lean_object* v_a_3302_ = stack[4].m_obj;
lean_object* v_res_3349_;
v_res_3349_ = l_Lean_Meta_isMonadApp(v_type_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
stack->m_obj
 = v_res_3349_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Meta_isMonadApp(v_type_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
return v_res_3356_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3357_, lean_object* v_opt_3358_){
_start:
{
lean_object* v_name_3359_; lean_object* v_defValue_3360_; lean_object* v_map_3361_; lean_object* v___x_3362_; 
v_name_3359_ = lean_ctor_get(v_opt_3358_, 0);
v_defValue_3360_ = lean_ctor_get(v_opt_3358_, 1);
v_map_3361_ = lean_ctor_get(v_opts_3357_, 0);
v___x_3362_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3361_, v_name_3359_);
if (lean_obj_tag(v___x_3362_) == 0)
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_unbox(v_defValue_3360_);
return v___x_3363_;
}
else
{
lean_object* v_val_3364_; 
v_val_3364_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_val_3364_);
lean_dec_ref_known(v___x_3362_, 1);
if (lean_obj_tag(v_val_3364_) == 1)
{
uint8_t v_v_3365_; 
v_v_3365_ = lean_ctor_get_uint8(v_val_3364_, 0);
lean_dec_ref_known(v_val_3364_, 0);
return v_v_3365_;
}
else
{
uint8_t v___x_3366_; 
lean_dec(v_val_3364_);
v___x_3366_ = lean_unbox(v_defValue_3360_);
return v___x_3366_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_3357_ = stack[0].m_obj;
lean_object* v_opt_3358_ = stack[1].m_obj;
uint8_t v_res_3367_;
v_res_3367_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3357_, v_opt_3358_);
stack->m_num = v_res_3367_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3368_, lean_object* v_opt_3369_){
_start:
{
uint8_t v_res_3370_; lean_object* v_r_3371_; 
v_res_3370_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3368_, v_opt_3369_);
lean_dec_ref(v_opt_3369_);
lean_dec_ref(v_opts_3368_);
v_r_3371_ = lean_box(v_res_3370_);
return v_r_3371_;
}
}
lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
return v___x_3381_;
}
}
LEAN_EXPORT void l_Lean_Meta_coerceMonadLift_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3374_ = stack[0].m_obj;
lean_object* v___y_3375_ = stack[1].m_obj;
lean_object* v___y_3376_ = stack[2].m_obj;
lean_object* v___y_3377_ = stack[3].m_obj;
lean_object* v___y_3378_ = stack[4].m_obj;
lean_object* v_res_3382_;
v_res_3382_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
stack->m_obj
 = v_res_3382_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec_ref(v_x_3383_);
return v_res_3389_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = lean_unsigned_to_nat(0u);
v___x_3400_ = l_Lean_mkBVar(v___x_3399_);
return v___x_3400_;
}
}
lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3412_, lean_object* v_expectedType_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_){
_start:
{
lean_object* v___y_3420_; uint8_t v___y_3421_; lean_object* v_a_3426_; lean_object* v___y_3430_; lean_object* v___x_3440_; lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3844_; 
v___x_3440_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3413_, v_a_3415_);
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3844_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3844_;
goto v_resetjp_3442_;
}
v___jp_3419_:
{
if (v___y_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec_ref(v___y_3420_);
v___x_3422_ = lean_box(0);
v___x_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
return v___x_3423_;
}
else
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___y_3420_);
return v___x_3424_;
}
}
v___jp_3425_:
{
uint8_t v___x_3427_; 
v___x_3427_ = l_Lean_Exception_isInterrupt(v_a_3426_);
if (v___x_3427_ == 0)
{
uint8_t v___x_3428_; 
lean_inc_ref(v_a_3426_);
v___x_3428_ = l_Lean_Exception_isRuntime(v_a_3426_);
v___y_3420_ = v_a_3426_;
v___y_3421_ = v___x_3428_;
goto v___jp_3419_;
}
else
{
v___y_3420_ = v_a_3426_;
v___y_3421_ = v___x_3427_;
goto v___jp_3419_;
}
}
v___jp_3429_:
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3439_; 
v_a_3431_ = lean_ctor_get(v___y_3430_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___y_3430_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3433_ = v___y_3430_;
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___y_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_a_3435_; lean_object* v___x_3437_; 
v_a_3435_ = lean_ctor_get(v_a_3431_, 0);
lean_inc(v_a_3435_);
lean_dec(v_a_3431_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v_a_3435_);
v___x_3437_ = v___x_3433_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; 
lean_inc(v_a_3417_);
lean_inc_ref(v_a_3416_);
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
lean_inc_ref(v_e_3412_);
v___x_3445_ = lean_infer_type(v_e_3412_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3835_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v___x_3447_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3446_, v_a_3415_);
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3835_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3835_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; 
lean_inc(v_a_3441_);
v___x_3452_ = l_Lean_Meta_isTypeApp_x3f(v_a_3441_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3826_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3826_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3826_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
if (lean_obj_tag(v_a_3453_) == 1)
{
lean_object* v_val_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3821_; 
lean_del_object(v___x_3455_);
v_val_3457_ = lean_ctor_get(v_a_3453_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_a_3453_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3459_ = v_a_3453_;
v_isShared_3460_ = v_isSharedCheck_3821_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_val_3457_);
lean_dec(v_a_3453_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3821_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v_fst_3461_; lean_object* v_snd_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3820_; 
v_fst_3461_ = lean_ctor_get(v_val_3457_, 0);
v_snd_3462_ = lean_ctor_get(v_val_3457_, 1);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_val_3457_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3464_ = v_val_3457_;
v_isShared_3465_ = v_isSharedCheck_3820_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_snd_3462_);
lean_inc(v_fst_3461_);
lean_dec(v_val_3457_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3820_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; 
lean_inc(v_a_3448_);
v___x_3466_ = l_Lean_Meta_isTypeApp_x3f(v_a_3448_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3811_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3811_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3811_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
if (lean_obj_tag(v_a_3467_) == 1)
{
lean_object* v_val_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3806_; 
lean_del_object(v___x_3469_);
v_val_3471_ = lean_ctor_get(v_a_3467_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_a_3467_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3473_ = v_a_3467_;
v_isShared_3474_ = v_isSharedCheck_3806_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_val_3471_);
lean_dec(v_a_3467_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3806_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v_fst_3475_; lean_object* v_snd_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3805_; 
v_fst_3475_ = lean_ctor_get(v_val_3471_, 0);
v_snd_3476_ = lean_ctor_get(v_val_3471_, 1);
v_isSharedCheck_3805_ = !lean_is_exclusive(v_val_3471_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3478_ = v_val_3471_;
v_isShared_3479_ = v_isSharedCheck_3805_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_snd_3476_);
lean_inc(v_fst_3475_);
lean_dec(v_val_3471_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3805_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_Meta_saveState___redArg(v_a_3415_, v_a_3417_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3482_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v___x_3480_, 1);
lean_inc(v_fst_3461_);
lean_inc(v_fst_3475_);
v___x_3482_ = l_Lean_Meta_isExprDefEq(v_fst_3475_, v_fst_3461_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3788_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3485_ = v___x_3482_;
v_isShared_3486_ = v_isSharedCheck_3788_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3788_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
uint8_t v___x_3487_; 
v___x_3487_ = lean_unbox(v_a_3483_);
lean_dec(v_a_3483_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
lean_dec(v_a_3481_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3450_);
lean_del_object(v___x_3443_);
v___x_3488_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3416_);
v___x_3489_ = l_Lean_Meta_autoLift;
v___x_3490_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v___x_3488_, v___x_3489_);
lean_dec_ref(v___x_3488_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3493_; 
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v___x_3491_ = lean_box(0);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3491_);
v___x_3493_ = v___x_3485_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
else
{
lean_object* v___x_3495_; 
lean_del_object(v___x_3485_);
lean_inc(v_a_3417_);
lean_inc_ref(v_a_3416_);
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
lean_inc(v_fst_3475_);
v___x_3495_ = lean_infer_type(v_fst_3475_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
lean_inc(v_a_3417_);
lean_inc_ref(v_a_3416_);
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
v___x_3497_ = lean_whnf(v_a_3496_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
if (lean_obj_tag(v_a_3498_) == 7)
{
lean_object* v_binderType_3499_; 
v_binderType_3499_ = lean_ctor_get(v_a_3498_, 1);
if (lean_obj_tag(v_binderType_3499_) == 3)
{
lean_object* v_body_3500_; 
v_body_3500_ = lean_ctor_get(v_a_3498_, 2);
if (lean_obj_tag(v_body_3500_) == 3)
{
lean_object* v_u_3501_; lean_object* v_u_3502_; lean_object* v___x_3503_; 
lean_inc_ref(v_body_3500_);
lean_inc_ref(v_binderType_3499_);
lean_dec_ref_known(v_a_3498_, 3);
v_u_3501_ = lean_ctor_get(v_binderType_3499_, 0);
lean_inc(v_u_3501_);
lean_dec_ref_known(v_binderType_3499_, 1);
v_u_3502_ = lean_ctor_get(v_body_3500_, 0);
lean_inc(v_u_3502_);
lean_dec_ref_known(v_body_3500_, 1);
lean_inc(v_a_3417_);
lean_inc_ref(v_a_3416_);
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
lean_inc(v_fst_3461_);
v___x_3503_ = lean_infer_type(v_fst_3461_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
lean_inc(v_a_3417_);
lean_inc_ref(v_a_3416_);
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
v___x_3505_ = lean_whnf(v_a_3504_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
if (lean_obj_tag(v_a_3506_) == 7)
{
lean_object* v_binderType_3507_; 
v_binderType_3507_ = lean_ctor_get(v_a_3506_, 1);
if (lean_obj_tag(v_binderType_3507_) == 3)
{
lean_object* v_body_3508_; 
v_body_3508_ = lean_ctor_get(v_a_3506_, 2);
if (lean_obj_tag(v_body_3508_) == 3)
{
lean_object* v_u_3509_; lean_object* v_u_3510_; lean_object* v___x_3511_; 
lean_inc_ref(v_body_3508_);
lean_inc_ref(v_binderType_3507_);
lean_dec_ref_known(v_a_3506_, 3);
v_u_3509_ = lean_ctor_get(v_binderType_3507_, 0);
lean_inc(v_u_3509_);
lean_dec_ref_known(v_binderType_3507_, 1);
v_u_3510_ = lean_ctor_get(v_body_3508_, 0);
lean_inc(v_u_3510_);
lean_dec_ref_known(v_body_3508_, 1);
v___x_3511_ = l_Lean_Meta_decLevel(v_u_3501_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = l_Lean_Meta_decLevel(v_u_3509_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
lean_inc(v_a_3512_);
v___x_3515_ = l_Lean_Meta_isLevelDefEq(v_a_3512_, v_a_3514_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3680_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3680_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3680_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
uint8_t v___x_3520_; 
v___x_3520_ = lean_unbox(v_a_3516_);
lean_dec(v_a_3516_);
if (v___x_3520_ == 1)
{
lean_object* v___x_3521_; 
lean_del_object(v___x_3518_);
v___x_3521_ = l_Lean_Meta_decLevel(v_u_3502_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3523_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = l_Lean_Meta_decLevel(v_u_3510_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v___x_3525_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3526_ = lean_box(0);
if (v_isShared_3479_ == 0)
{
lean_ctor_set_tag(v___x_3478_, 1);
lean_ctor_set(v___x_3478_, 1, v___x_3526_);
lean_ctor_set(v___x_3478_, 0, v_a_3524_);
v___x_3528_ = v___x_3478_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3524_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3530_; 
if (v_isShared_3465_ == 0)
{
lean_ctor_set_tag(v___x_3464_, 1);
lean_ctor_set(v___x_3464_, 1, v___x_3528_);
lean_ctor_set(v___x_3464_, 0, v_a_3522_);
v___x_3530_ = v___x_3464_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3522_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3531_, 0, v_a_3512_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = l_Lean_Expr_const___override(v___x_3525_, v___x_3531_);
v___x_3533_ = lean_unsigned_to_nat(2u);
v___x_3534_ = lean_mk_empty_array_with_capacity(v___x_3533_);
lean_inc(v_fst_3475_);
v___x_3535_ = lean_array_push(v___x_3534_, v_fst_3475_);
lean_inc(v_fst_3461_);
v___x_3536_ = lean_array_push(v___x_3535_, v_fst_3461_);
v___x_3537_ = l_Lean_mkAppN(v___x_3532_, v___x_3536_);
lean_dec_ref(v___x_3536_);
v___x_3538_ = lean_box(0);
v___x_3539_ = l_Lean_Meta_trySynthInstance(v___x_3537_, v___x_3538_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3670_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3670_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3670_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
if (lean_obj_tag(v_a_3540_) == 1)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; 
lean_del_object(v___x_3542_);
v_a_3544_ = lean_ctor_get(v_a_3540_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v_a_3540_, 1);
lean_inc(v_snd_3476_);
v___x_3545_ = l_Lean_Meta_getDecLevel(v_snd_3476_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v___x_3547_ = l_Lean_Meta_getDecLevel(v_a_3448_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3549_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
lean_inc(v_a_3441_);
v___x_3549_ = l_Lean_Meta_getDecLevel(v_a_3441_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3549_, 1);
v___x_3551_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3552_, 0, v_a_3550_);
lean_ctor_set(v___x_3552_, 1, v___x_3526_);
v___x_3553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3553_, 0, v_a_3548_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3554_, 0, v_a_3546_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
lean_inc_ref(v___x_3554_);
v___x_3555_ = l_Lean_mkConst(v___x_3551_, v___x_3554_);
v___x_3556_ = lean_unsigned_to_nat(5u);
v___x_3557_ = lean_mk_empty_array_with_capacity(v___x_3556_);
lean_inc(v_fst_3475_);
v___x_3558_ = lean_array_push(v___x_3557_, v_fst_3475_);
lean_inc(v_fst_3461_);
v___x_3559_ = lean_array_push(v___x_3558_, v_fst_3461_);
lean_inc(v_a_3544_);
v___x_3560_ = lean_array_push(v___x_3559_, v_a_3544_);
lean_inc(v_snd_3476_);
v___x_3561_ = lean_array_push(v___x_3560_, v_snd_3476_);
lean_inc_ref(v_e_3412_);
v___x_3562_ = lean_array_push(v___x_3561_, v_e_3412_);
v___x_3563_ = l_Lean_mkAppN(v___x_3555_, v___x_3562_);
lean_dec_ref(v___x_3562_);
lean_inc(v_a_3417_);
lean_inc_ref(v_a_3416_);
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
lean_inc_ref(v___x_3563_);
v___x_3564_ = lean_infer_type(v___x_3563_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3566_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3564_, 1);
lean_inc(v_a_3441_);
v___x_3566_ = l_Lean_Meta_isExprDefEq(v_a_3441_, v_a_3565_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3661_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3661_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3661_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
uint8_t v___x_3571_; 
v___x_3571_ = lean_unbox(v_a_3567_);
lean_dec(v_a_3567_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; 
lean_del_object(v___x_3569_);
lean_dec_ref(v___x_3563_);
lean_del_object(v___x_3473_);
lean_inc(v_fst_3461_);
v___x_3572_ = l_Lean_Meta_isMonad_x3f(v_fst_3461_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3653_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3575_ = v___x_3572_;
v_isShared_3576_ = v_isSharedCheck_3653_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3653_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
if (lean_obj_tag(v_a_3573_) == 1)
{
lean_object* v_val_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3649_; 
lean_del_object(v___x_3575_);
v_val_3577_ = lean_ctor_get(v_a_3573_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_a_3573_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3579_ = v_a_3573_;
v_isShared_3580_ = v_isSharedCheck_3649_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_val_3577_);
lean_dec(v_a_3573_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3649_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; 
lean_inc(v_snd_3476_);
v___x_3581_ = l_Lean_Meta_getLevel(v_snd_3476_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3583_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
lean_inc(v_snd_3462_);
v___x_3583_ = l_Lean_Meta_getLevel(v_snd_3462_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___x_3583_, 1);
v___x_3585_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3586_ = 0;
v___x_3587_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3588_, 0, v_a_3584_);
lean_ctor_set(v___x_3588_, 1, v___x_3526_);
v___x_3589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3589_, 0, v_a_3582_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = l_Lean_mkConst(v___x_3587_, v___x_3589_);
v___x_3591_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3592_ = lean_unsigned_to_nat(3u);
v___x_3593_ = lean_mk_empty_array_with_capacity(v___x_3592_);
lean_inc_n(v_snd_3476_, 2);
v___x_3594_ = lean_array_push(v___x_3593_, v_snd_3476_);
v___x_3595_ = lean_array_push(v___x_3594_, v___x_3591_);
lean_inc(v_snd_3462_);
v___x_3596_ = lean_array_push(v___x_3595_, v_snd_3462_);
v___x_3597_ = l_Lean_mkAppN(v___x_3590_, v___x_3596_);
lean_dec_ref(v___x_3596_);
v___x_3598_ = l_Lean_mkForall(v___x_3585_, v___x_3586_, v_snd_3476_, v___x_3597_);
v___x_3599_ = l_Lean_Meta_trySynthInstance(v___x_3598_, v___x_3538_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3645_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3602_ = v___x_3599_;
v_isShared_3603_ = v_isSharedCheck_3645_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3599_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3645_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
if (lean_obj_tag(v_a_3600_) == 1)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_del_object(v___x_3602_);
v_a_3604_ = lean_ctor_get(v_a_3600_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v_a_3600_, 1);
v___x_3605_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3606_ = l_Lean_mkConst(v___x_3605_, v___x_3554_);
v___x_3607_ = lean_unsigned_to_nat(8u);
v___x_3608_ = lean_mk_empty_array_with_capacity(v___x_3607_);
v___x_3609_ = lean_array_push(v___x_3608_, v_fst_3475_);
v___x_3610_ = lean_array_push(v___x_3609_, v_fst_3461_);
v___x_3611_ = lean_array_push(v___x_3610_, v_snd_3476_);
v___x_3612_ = lean_array_push(v___x_3611_, v_snd_3462_);
v___x_3613_ = lean_array_push(v___x_3612_, v_a_3544_);
v___x_3614_ = lean_array_push(v___x_3613_, v_a_3604_);
v___x_3615_ = lean_array_push(v___x_3614_, v_val_3577_);
v___x_3616_ = lean_array_push(v___x_3615_, v_e_3412_);
v___x_3617_ = l_Lean_mkAppN(v___x_3606_, v___x_3616_);
lean_dec_ref(v___x_3616_);
v___x_3618_ = l_Lean_Meta_expandCoe(v___x_3617_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v_fst_3620_; lean_object* v___x_3621_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v_fst_3620_ = lean_ctor_get(v_a_3619_, 0);
lean_inc_n(v_fst_3620_, 2);
lean_dec(v_a_3619_);
lean_inc(v_a_3417_);
lean_inc_ref(v_a_3416_);
lean_inc(v_a_3415_);
lean_inc_ref(v_a_3414_);
v___x_3621_ = lean_infer_type(v_fst_3620_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3623_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
lean_dec_ref_known(v___x_3621_, 1);
v___x_3623_ = l_Lean_Meta_isExprDefEq(v_a_3441_, v_a_3622_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3638_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3638_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3638_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
uint8_t v___x_3628_; 
v___x_3628_ = lean_unbox(v_a_3624_);
lean_dec(v_a_3624_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3630_; 
lean_dec(v_fst_3620_);
lean_del_object(v___x_3579_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v___x_3538_);
v___x_3630_ = v___x_3626_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3538_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
else
{
lean_object* v___x_3633_; 
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v_fst_3620_);
v___x_3633_ = v___x_3579_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_fst_3620_);
v___x_3633_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3635_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v___x_3633_);
v___x_3635_ = v___x_3626_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
else
{
lean_object* v_a_3639_; 
lean_dec(v_fst_3620_);
lean_del_object(v___x_3579_);
v_a_3639_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3623_, 1);
v_a_3426_ = v_a_3639_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3640_; 
lean_dec(v_fst_3620_);
lean_del_object(v___x_3579_);
lean_dec(v_a_3441_);
v_a_3640_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3621_, 1);
v_a_3426_ = v_a_3640_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3641_; 
lean_del_object(v___x_3579_);
lean_dec(v_a_3441_);
v_a_3641_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3641_);
lean_dec_ref_known(v___x_3618_, 1);
v_a_3426_ = v_a_3641_;
goto v___jp_3425_;
}
}
else
{
lean_object* v___x_3643_; 
lean_dec(v_a_3600_);
lean_del_object(v___x_3579_);
lean_dec(v_val_3577_);
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v___x_3538_);
v___x_3643_ = v___x_3602_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3538_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_a_3646_; 
lean_del_object(v___x_3579_);
lean_dec(v_val_3577_);
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3646_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v___x_3599_, 1);
v_a_3426_ = v_a_3646_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3647_; 
lean_dec(v_a_3582_);
lean_del_object(v___x_3579_);
lean_dec(v_val_3577_);
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3647_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v___x_3583_, 1);
v_a_3426_ = v_a_3647_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3648_; 
lean_del_object(v___x_3579_);
lean_dec(v_val_3577_);
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3648_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3648_);
lean_dec_ref_known(v___x_3581_, 1);
v_a_3426_ = v_a_3648_;
goto v___jp_3425_;
}
}
}
else
{
lean_object* v___x_3651_; 
lean_dec(v_a_3573_);
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3538_);
v___x_3651_ = v___x_3575_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3538_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
else
{
lean_object* v_a_3654_; 
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3654_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3572_, 1);
v_a_3426_ = v_a_3654_;
goto v___jp_3425_;
}
}
else
{
lean_object* v___x_3656_; 
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3563_);
v___x_3656_ = v___x_3473_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3563_);
v___x_3656_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3656_);
v___x_3658_ = v___x_3569_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3656_);
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
}
else
{
lean_object* v_a_3662_; 
lean_dec_ref(v___x_3563_);
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3662_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3566_, 1);
v_a_3426_ = v_a_3662_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3663_; 
lean_dec_ref(v___x_3563_);
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3663_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3564_, 1);
v_a_3426_ = v_a_3663_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3664_; 
lean_dec(v_a_3548_);
lean_dec(v_a_3546_);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3664_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3549_, 1);
v_a_3426_ = v_a_3664_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3665_; 
lean_dec(v_a_3546_);
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3665_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3547_, 1);
v_a_3426_ = v_a_3665_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3666_; 
lean_dec(v_a_3544_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3666_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3545_, 1);
v_a_3426_ = v_a_3666_;
goto v___jp_3425_;
}
}
else
{
lean_object* v___x_3668_; 
lean_dec(v_a_3540_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3538_);
v___x_3668_ = v___x_3542_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3538_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
else
{
lean_object* v_a_3671_; 
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3671_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3539_, 1);
v_a_3426_ = v_a_3671_;
goto v___jp_3425_;
}
}
}
}
else
{
lean_object* v_a_3674_; 
lean_dec(v_a_3522_);
lean_dec(v_a_3512_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3674_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3674_);
lean_dec_ref_known(v___x_3523_, 1);
v_a_3426_ = v_a_3674_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3675_; 
lean_dec(v_a_3512_);
lean_dec(v_u_3510_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3675_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3675_);
lean_dec_ref_known(v___x_3521_, 1);
v_a_3426_ = v_a_3675_;
goto v___jp_3425_;
}
}
else
{
lean_object* v___x_3676_; lean_object* v___x_3678_; 
lean_dec(v_a_3512_);
lean_dec(v_u_3510_);
lean_dec(v_u_3502_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v___x_3676_ = lean_box(0);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3676_);
v___x_3678_ = v___x_3518_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3681_; 
lean_dec(v_a_3512_);
lean_dec(v_u_3510_);
lean_dec(v_u_3502_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3681_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3515_, 1);
v_a_3426_ = v_a_3681_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3682_; 
lean_dec(v_a_3512_);
lean_dec(v_u_3510_);
lean_dec(v_u_3502_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3682_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3682_);
lean_dec_ref_known(v___x_3513_, 1);
v_a_3426_ = v_a_3682_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3683_; 
lean_dec(v_u_3510_);
lean_dec(v_u_3509_);
lean_dec(v_u_3502_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3683_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3511_, 1);
v_a_3426_ = v_a_3683_;
goto v___jp_3425_;
}
}
else
{
lean_object* v___x_3684_; 
lean_dec(v_u_3502_);
lean_dec(v_u_3501_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v___x_3684_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3506_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec_ref_known(v_a_3506_, 3);
v___y_3430_ = v___x_3684_;
goto v___jp_3429_;
}
}
else
{
lean_object* v___x_3685_; 
lean_dec(v_u_3502_);
lean_dec(v_u_3501_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v___x_3685_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3506_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec_ref_known(v_a_3506_, 3);
v___y_3430_ = v___x_3685_;
goto v___jp_3429_;
}
}
else
{
lean_object* v___x_3686_; 
lean_dec(v_u_3502_);
lean_dec(v_u_3501_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v___x_3686_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3506_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec(v_a_3506_);
v___y_3430_ = v___x_3686_;
goto v___jp_3429_;
}
}
else
{
lean_object* v_a_3687_; 
lean_dec(v_u_3502_);
lean_dec(v_u_3501_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3687_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3505_, 1);
v_a_3426_ = v_a_3687_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3688_; 
lean_dec(v_u_3502_);
lean_dec(v_u_3501_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3688_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3503_, 1);
v_a_3426_ = v_a_3688_;
goto v___jp_3425_;
}
}
else
{
lean_object* v___x_3689_; 
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v___x_3689_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3498_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec_ref_known(v_a_3498_, 3);
v___y_3430_ = v___x_3689_;
goto v___jp_3429_;
}
}
else
{
lean_object* v___x_3690_; 
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v___x_3690_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3498_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec_ref_known(v_a_3498_, 3);
v___y_3430_ = v___x_3690_;
goto v___jp_3429_;
}
}
else
{
lean_object* v___x_3691_; 
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v___x_3691_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3498_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec(v_a_3498_);
v___y_3430_ = v___x_3691_;
goto v___jp_3429_;
}
}
else
{
lean_object* v_a_3692_; 
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3692_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3692_);
lean_dec_ref_known(v___x_3497_, 1);
v_a_3426_ = v_a_3692_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3693_; 
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3693_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3495_, 1);
v_a_3426_ = v_a_3693_;
goto v___jp_3425_;
}
}
}
else
{
lean_object* v___x_3694_; 
lean_del_object(v___x_3485_);
lean_del_object(v___x_3478_);
lean_del_object(v___x_3464_);
lean_dec(v_a_3448_);
lean_dec(v_a_3441_);
v___x_3694_ = l_Lean_Meta_isMonad_x3f(v_fst_3461_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3787_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3697_ = v___x_3694_;
v_isShared_3698_ = v_isSharedCheck_3787_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3787_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
if (lean_obj_tag(v_a_3695_) == 1)
{
lean_object* v___x_3699_; lean_object* v___x_3701_; 
v___x_3699_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v_fst_3475_);
v___x_3701_ = v___x_3473_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_fst_3475_);
v___x_3701_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
lean_object* v___x_3703_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v_snd_3476_);
v___x_3703_ = v___x_3459_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_snd_3476_);
v___x_3703_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3705_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set_tag(v___x_3450_, 1);
lean_ctor_set(v___x_3450_, 0, v_snd_3462_);
v___x_3705_ = v___x_3450_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_snd_3462_);
v___x_3705_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; lean_object* v___y_3708_; uint8_t v___y_3709_; lean_object* v_a_3731_; lean_object* v___x_3735_; 
v___x_3706_ = lean_box(0);
if (v_isShared_3444_ == 0)
{
lean_ctor_set_tag(v___x_3443_, 1);
lean_ctor_set(v___x_3443_, 0, v_e_3412_);
v___x_3735_ = v___x_3443_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_e_3412_);
v___x_3735_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3734_;
}
v___jp_3707_:
{
if (v___y_3709_ == 0)
{
lean_object* v___x_3710_; 
lean_dec_ref(v___y_3708_);
lean_del_object(v___x_3697_);
v___x_3710_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3481_, v_a_3415_, v_a_3417_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3717_ == 0)
{
lean_object* v_unused_3718_; 
v_unused_3718_ = lean_ctor_get(v___x_3710_, 0);
lean_dec(v_unused_3718_);
v___x_3712_ = v___x_3710_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_dec(v___x_3710_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3706_);
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3706_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
v_a_3719_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3710_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3710_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
else
{
lean_object* v___x_3728_; 
lean_dec(v_a_3481_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set_tag(v___x_3697_, 1);
lean_ctor_set(v___x_3697_, 0, v___y_3708_);
v___x_3728_ = v___x_3697_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___y_3708_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
v___jp_3730_:
{
uint8_t v___x_3732_; 
v___x_3732_ = l_Lean_Exception_isInterrupt(v_a_3731_);
if (v___x_3732_ == 0)
{
uint8_t v___x_3733_; 
lean_inc_ref(v_a_3731_);
v___x_3733_ = l_Lean_Exception_isRuntime(v_a_3731_);
v___y_3708_ = v_a_3731_;
v___y_3709_ = v___x_3733_;
goto v___jp_3707_;
}
else
{
v___y_3708_ = v_a_3731_;
v___y_3709_ = v___x_3732_;
goto v___jp_3707_;
}
}
v_reusejp_3734_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3736_ = lean_unsigned_to_nat(6u);
v___x_3737_ = lean_mk_empty_array_with_capacity(v___x_3736_);
v___x_3738_ = lean_array_push(v___x_3737_, v___x_3701_);
v___x_3739_ = lean_array_push(v___x_3738_, v___x_3703_);
v___x_3740_ = lean_array_push(v___x_3739_, v___x_3705_);
v___x_3741_ = lean_array_push(v___x_3740_, v___x_3706_);
v___x_3742_ = lean_array_push(v___x_3741_, v_a_3695_);
v___x_3743_ = lean_array_push(v___x_3742_, v___x_3735_);
v___x_3744_ = l_Lean_Meta_mkAppOptM(v___x_3699_, v___x_3743_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3763_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3747_ = v___x_3744_;
v_isShared_3748_ = v_isSharedCheck_3763_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3763_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_Meta_expandCoe(v_a_3745_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3761_; 
lean_del_object(v___x_3697_);
lean_dec(v_a_3481_);
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3752_ = v___x_3749_;
v_isShared_3753_ = v_isSharedCheck_3761_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3749_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3761_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v_fst_3754_; lean_object* v___x_3756_; 
v_fst_3754_ = lean_ctor_get(v_a_3750_, 0);
lean_inc(v_fst_3754_);
lean_dec(v_a_3750_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set_tag(v___x_3747_, 1);
lean_ctor_set(v___x_3747_, 0, v_fst_3754_);
v___x_3756_ = v___x_3747_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_fst_3754_);
v___x_3756_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3756_);
v___x_3758_ = v___x_3752_;
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
lean_object* v_a_3762_; 
lean_del_object(v___x_3747_);
v_a_3762_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3749_, 1);
v_a_3731_ = v_a_3762_;
goto v___jp_3730_;
}
}
}
else
{
lean_object* v_a_3764_; 
v_a_3764_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3744_, 1);
v_a_3731_ = v_a_3764_;
goto v___jp_3730_;
}
}
}
}
}
}
else
{
lean_object* v___x_3769_; 
lean_del_object(v___x_3697_);
lean_dec(v_a_3695_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_dec(v_snd_3462_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3450_);
lean_del_object(v___x_3443_);
lean_dec_ref(v_e_3412_);
v___x_3769_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3481_, v_a_3415_, v_a_3417_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3777_; 
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3777_ == 0)
{
lean_object* v_unused_3778_; 
v_unused_3778_ = lean_ctor_get(v___x_3769_, 0);
lean_dec(v_unused_3778_);
v___x_3771_ = v___x_3769_;
v_isShared_3772_ = v_isSharedCheck_3777_;
goto v_resetjp_3770_;
}
else
{
lean_dec(v___x_3769_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3777_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3773_; lean_object* v___x_3775_; 
v___x_3773_ = lean_box(0);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 0, v___x_3773_);
v___x_3775_ = v___x_3771_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
v_a_3779_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3769_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3769_);
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
lean_dec(v_a_3481_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_dec(v_snd_3462_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3450_);
lean_del_object(v___x_3443_);
lean_dec_ref(v_e_3412_);
return v___x_3694_;
}
}
}
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec(v_a_3481_);
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3450_);
lean_dec(v_a_3448_);
lean_del_object(v___x_3443_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3789_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3482_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3482_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_del_object(v___x_3478_);
lean_dec(v_snd_3476_);
lean_dec(v_fst_3475_);
lean_del_object(v___x_3473_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3450_);
lean_dec(v_a_3448_);
lean_del_object(v___x_3443_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3797_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3480_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3480_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
lean_dec(v_a_3467_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3450_);
lean_dec(v_a_3448_);
lean_del_object(v___x_3443_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v___x_3807_ = lean_box(0);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3807_);
v___x_3809_ = v___x_3469_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3807_);
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
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3450_);
lean_dec(v_a_3448_);
lean_del_object(v___x_3443_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3812_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3466_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3466_);
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
lean_dec(v_a_3453_);
lean_del_object(v___x_3450_);
lean_dec(v_a_3448_);
lean_del_object(v___x_3443_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v___x_3822_ = lean_box(0);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3822_);
v___x_3824_ = v___x_3455_;
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
lean_del_object(v___x_3450_);
lean_dec(v_a_3448_);
lean_del_object(v___x_3443_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3827_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3452_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3452_);
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
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_del_object(v___x_3443_);
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3412_);
v_a_3836_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3445_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3445_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_coerceMonadLift_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3412_ = stack[0].m_obj;
lean_object* v_expectedType_3413_ = stack[1].m_obj;
lean_object* v_a_3414_ = stack[2].m_obj;
lean_object* v_a_3415_ = stack[3].m_obj;
lean_object* v_a_3416_ = stack[4].m_obj;
lean_object* v_a_3417_ = stack[5].m_obj;
lean_object* v_res_3845_;
v_res_3845_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3412_, v_expectedType_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
stack->m_obj
 = v_res_3845_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3846_, lean_object* v_expectedType_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3846_, v_expectedType_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec_ref(v_a_3848_);
return v_res_3853_;
}
}
lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3854_, lean_object* v_expectedType_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_){
_start:
{
lean_object* v___x_3861_; 
lean_inc_ref(v_expectedType_3855_);
lean_inc_ref(v_expr_3854_);
v___x_3861_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3854_, v_expectedType_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3941_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3941_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3941_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
if (lean_obj_tag(v_a_3862_) == 1)
{
lean_object* v_val_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3878_; 
lean_dec_ref(v_expectedType_3855_);
lean_dec_ref(v_expr_3854_);
v_val_3866_ = lean_ctor_get(v_a_3862_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_a_3862_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3868_ = v_a_3862_;
v_isShared_3869_ = v_isSharedCheck_3878_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_val_3866_);
lean_dec(v_a_3862_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3878_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3870_ = lean_box(0);
v___x_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3871_, 0, v_val_3866_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v___x_3871_);
v___x_3873_ = v___x_3868_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
lean_object* v___x_3875_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v___x_3873_);
v___x_3875_ = v___x_3864_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
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
else
{
lean_object* v___x_3879_; 
lean_del_object(v___x_3864_);
lean_dec(v_a_3862_);
lean_inc_ref(v_expectedType_3855_);
v___x_3879_ = l_Lean_Meta_whnfR(v_expectedType_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; uint8_t v___x_3881_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3881_ = l_Lean_Expr_isForall(v_a_3880_);
lean_dec(v_a_3880_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3854_, v_expectedType_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
return v___x_3882_;
}
else
{
lean_object* v___x_3883_; 
lean_inc_ref(v_expr_3854_);
v___x_3883_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3854_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
if (lean_obj_tag(v_a_3884_) == 1)
{
lean_object* v_val_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3923_; 
v_val_3885_ = lean_ctor_get(v_a_3884_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_a_3884_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3887_ = v_a_3884_;
v_isShared_3888_ = v_isSharedCheck_3923_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_val_3885_);
lean_dec(v_a_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3923_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; 
lean_inc(v_a_3859_);
lean_inc_ref(v_a_3858_);
lean_inc(v_a_3857_);
lean_inc_ref(v_a_3856_);
lean_inc(v_val_3885_);
v___x_3889_ = lean_infer_type(v_val_3885_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___x_3891_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3889_, 1);
lean_inc_ref(v_expectedType_3855_);
v___x_3891_ = l_Lean_Meta_isExprDefEq(v_a_3890_, v_expectedType_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3906_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3894_ = v___x_3891_;
v_isShared_3895_ = v_isSharedCheck_3906_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3906_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
uint8_t v___x_3896_; 
v___x_3896_ = lean_unbox(v_a_3892_);
lean_dec(v_a_3892_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3897_; 
lean_del_object(v___x_3894_);
lean_del_object(v___x_3887_);
lean_dec(v_val_3885_);
v___x_3897_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3854_, v_expectedType_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
return v___x_3897_;
}
else
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3901_; 
lean_dec_ref(v_expectedType_3855_);
lean_dec_ref(v_expr_3854_);
v___x_3898_ = lean_box(0);
v___x_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3899_, 0, v_val_3885_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v___x_3899_);
v___x_3901_ = v___x_3887_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3899_);
v___x_3901_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
lean_object* v___x_3903_; 
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___x_3901_);
v___x_3903_ = v___x_3894_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_del_object(v___x_3887_);
lean_dec(v_val_3885_);
lean_dec_ref(v_expectedType_3855_);
lean_dec_ref(v_expr_3854_);
v_a_3907_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3891_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3891_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_del_object(v___x_3887_);
lean_dec(v_val_3885_);
lean_dec_ref(v_expectedType_3855_);
lean_dec_ref(v_expr_3854_);
v_a_3915_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3889_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3889_);
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
lean_object* v___x_3924_; 
lean_dec(v_a_3884_);
v___x_3924_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3854_, v_expectedType_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
return v___x_3924_;
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec_ref(v_expectedType_3855_);
lean_dec_ref(v_expr_3854_);
v_a_3925_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3883_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3883_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
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
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec_ref(v_expectedType_3855_);
lean_dec_ref(v_expr_3854_);
v_a_3933_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3879_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3879_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec_ref(v_expectedType_3855_);
lean_dec_ref(v_expr_3854_);
v_a_3942_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3861_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3861_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_coerceCollectingNames_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_3854_ = stack[0].m_obj;
lean_object* v_expectedType_3855_ = stack[1].m_obj;
lean_object* v_a_3856_ = stack[2].m_obj;
lean_object* v_a_3857_ = stack[3].m_obj;
lean_object* v_a_3858_ = stack[4].m_obj;
lean_object* v_a_3859_ = stack[5].m_obj;
lean_object* v_res_3950_;
v_res_3950_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3854_, v_expectedType_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
stack->m_obj
 = v_res_3950_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3951_, lean_object* v_expectedType_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3951_, v_expectedType_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
lean_dec(v_a_3956_);
lean_dec_ref(v_a_3955_);
lean_dec(v_a_3954_);
lean_dec_ref(v_a_3953_);
return v_res_3958_;
}
}
lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3959_, lean_object* v_expectedType_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3959_, v_expectedType_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3991_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3969_ = v___x_3966_;
v_isShared_3970_ = v_isSharedCheck_3991_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3966_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3991_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
switch(lean_obj_tag(v_a_3967_))
{
case 0:
{
lean_object* v___x_3971_; lean_object* v___x_3973_; 
v___x_3971_ = lean_box(0);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3971_);
v___x_3973_ = v___x_3969_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
case 1:
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3986_; 
v_a_3975_ = lean_ctor_get(v_a_3967_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v_a_3967_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3977_ = v_a_3967_;
v_isShared_3978_ = v_isSharedCheck_3986_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v_a_3967_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3986_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v_fst_3979_; lean_object* v___x_3981_; 
v_fst_3979_ = lean_ctor_get(v_a_3975_, 0);
lean_inc(v_fst_3979_);
lean_dec(v_a_3975_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v_fst_3979_);
v___x_3981_ = v___x_3977_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_fst_3979_);
v___x_3981_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3983_; 
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3981_);
v___x_3983_ = v___x_3969_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
default: 
{
lean_object* v___x_3987_; lean_object* v___x_3989_; 
v___x_3987_ = lean_box(2);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3987_);
v___x_3989_ = v___x_3969_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
v_a_3992_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3966_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3966_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_coerce_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_3959_ = stack[0].m_obj;
lean_object* v_expectedType_3960_ = stack[1].m_obj;
lean_object* v_a_3961_ = stack[2].m_obj;
lean_object* v_a_3962_ = stack[3].m_obj;
lean_object* v_a_3963_ = stack[4].m_obj;
lean_object* v_a_3964_ = stack[5].m_obj;
lean_object* v_res_4000_;
v_res_4000_ = l_Lean_Meta_coerce_x3f(v_expr_3959_, v_expectedType_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
stack->m_obj
 = v_res_4000_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_4001_, lean_object* v_expectedType_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_Meta_coerce_x3f(v_expr_4001_, v_expectedType_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
lean_dec(v_a_4006_);
lean_dec_ref(v_a_4005_);
lean_dec(v_a_4004_);
lean_dec_ref(v_a_4003_);
return v_res_4008_;
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
