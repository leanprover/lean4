// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Attr
// Imports: public import Lean.Meta.Tactic.Simp public import Std.Tactic.Do.Syntax import Init.While import Init.Syntax
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_getBuiltinAttributeImpl(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "specAttr"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 104, 229, 54, 179, 197, 12, 87)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 227, 209, 95, 37, 139, 151, 115)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 242, 56, 182, 153, 42, 114, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 138, 236, 57, 102, 124, 147, 255)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(28, 143, 222, 144, 140, 210, 107, 73)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 241, 13, 86, 234, 108, 15, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 82, 232, 142, 6, 30, 251, 218)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 109, 34, 147, 49, 200, 3, 39)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 221, 137, 6, 209, 179, 60, 120)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "SpecAttr"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 26, 34, 181, 184, 226, 120, 151)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 187, 149, 116, 143, 76, 116, 236)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(29, 168, 76, 208, 197, 143, 217, 95)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 148, 5, 92, 126, 87, 141, 58)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 170, 239, 49, 120, 133, 251, 59)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 191, 110, 138, 35, 85, 164, 132)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(115, 82, 114, 61, 251, 7, 76, 52)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 252, 214, 90, 155, 123, 70, 139)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1315642830) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(123, 62, 96, 72, 129, 246, 18, 82)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 191, 233, 209, 139, 48, 252, 140)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 32, 213, 31, 56, 138, 46, 85)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(61, 54, 255, 31, 21, 96, 7, 214)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mvcgen_simp"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 132, 230, 222, 36, 150, 155, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "simp theorems internally used by `mvcgen`"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mvcgenSimpExt"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 109, 122, 82, 215, 148, 2, 116)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(15, 64, 145, 249, 56, 70, 6, 95)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_global_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_global_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_local_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_local_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_stx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_stx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0;
LEAN_EXPORT uint64_t l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SpecProof.global "};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.local "};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.stx _ "};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3(lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__2_value;
static const lean_array_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "unexpected kind of spec theorem; not a triple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(31, 48, 165, 224, 255, 99, 7, 166)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PostShape"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "args"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(1, 175, 203, 13, 190, 221, 208, 89)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(91, 155, 250, 91, 111, 213, 166, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "invalid 'spec', proposition expected"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "invalid 'spec', local declaration "};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " not found"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "specMap"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3_value),LEAN_SCALAR_PTR_LITERAL(12, 125, 237, 218, 61, 113, 214, 206)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "Invalid 'spec': target was neither a Hoare triple specification nor a 'simp' lemma"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5;
static const lean_array_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Reason for failure to apply spec attribute: "};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mkSpecAttr"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 109, 122, 82, 215, 148, 2, 116)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(131, 130, 97, 217, 238, 242, 98, 155)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "spec"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 105, 220, 149, 84, 64, 243, 129)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "Marks Hoare triple specifications and simp theorems to use with the `mspec` and `mvcgen` tactics"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "spec_invariant_type"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 116, 165, 165, 49, 205, 9, 77)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "marks a type as an invariant type for the `mvcgen` tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "specInvariantAttr"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 109, 122, 82, 215, 148, 2, 116)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 249, 139, 62, 184, 94, 1, 139)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_89_ = 0;
v___x_90_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_91_ = l_Lean_registerTraceClass(v___x_88_, v___x_89_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2____boxed(lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_();
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_110_ = l_Lean_Meta_registerSimpAttr(v___x_107_, v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2____boxed(lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg(lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt;
v___x_116_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_115_, v_a_113_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg___boxed(lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg(v_a_117_);
lean_dec(v_a_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems(lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg(v_a_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___boxed(lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems(v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx(lean_object* v_x_128_){
_start:
{
switch(lean_obj_tag(v_x_128_))
{
case 0:
{
lean_object* v___x_129_; 
v___x_129_ = lean_unsigned_to_nat(0u);
return v___x_129_;
}
case 1:
{
lean_object* v___x_130_; 
v___x_130_ = lean_unsigned_to_nat(1u);
return v___x_130_;
}
default: 
{
lean_object* v___x_131_; 
v___x_131_ = lean_unsigned_to_nat(2u);
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx___boxed(lean_object* v_x_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx(v_x_132_);
lean_dec_ref(v_x_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(lean_object* v_t_134_, lean_object* v_k_135_){
_start:
{
if (lean_obj_tag(v_t_134_) == 2)
{
lean_object* v_id_136_; lean_object* v_ref_137_; lean_object* v_proof_138_; lean_object* v___x_139_; 
v_id_136_ = lean_ctor_get(v_t_134_, 0);
lean_inc(v_id_136_);
v_ref_137_ = lean_ctor_get(v_t_134_, 1);
lean_inc(v_ref_137_);
v_proof_138_ = lean_ctor_get(v_t_134_, 2);
lean_inc_ref(v_proof_138_);
lean_dec_ref(v_t_134_);
v___x_139_ = lean_apply_3(v_k_135_, v_id_136_, v_ref_137_, v_proof_138_);
return v___x_139_;
}
else
{
lean_object* v_declName_140_; lean_object* v___x_141_; 
v_declName_140_ = lean_ctor_get(v_t_134_, 0);
lean_inc(v_declName_140_);
lean_dec_ref(v_t_134_);
v___x_141_ = lean_apply_1(v_k_135_, v_declName_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim(lean_object* v_motive_142_, lean_object* v_ctorIdx_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_k_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_144_, v_k_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___boxed(lean_object* v_motive_148_, lean_object* v_ctorIdx_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_k_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim(v_motive_148_, v_ctorIdx_149_, v_t_150_, v_h_151_, v_k_152_);
lean_dec(v_ctorIdx_149_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_global_elim___redArg(lean_object* v_t_154_, lean_object* v_global_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_154_, v_global_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_global_elim(lean_object* v_motive_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_global_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_158_, v_global_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_local_elim___redArg(lean_object* v_t_162_, lean_object* v_local_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_162_, v_local_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_local_elim(lean_object* v_motive_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_local_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_166_, v_local_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_stx_elim___redArg(lean_object* v_t_170_, lean_object* v_stx_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_170_, v_stx_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_stx_elim(lean_object* v_motive_173_, lean_object* v_t_174_, lean_object* v_h_175_, lean_object* v_stx_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_174_, v_stx_176_);
return v___x_177_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
switch(lean_obj_tag(v_x_182_))
{
case 0:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v_declName_184_; lean_object* v_declName_185_; uint8_t v___x_186_; 
v_declName_184_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_declName_184_);
lean_dec_ref(v_x_182_);
v_declName_185_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_declName_185_);
lean_dec_ref(v_x_183_);
v___x_186_ = lean_name_eq(v_declName_184_, v_declName_185_);
lean_dec(v_declName_185_);
lean_dec(v_declName_184_);
return v___x_186_;
}
else
{
uint8_t v___x_187_; 
lean_dec_ref(v_x_182_);
lean_dec_ref(v_x_183_);
v___x_187_ = 0;
return v___x_187_;
}
}
case 1:
{
if (lean_obj_tag(v_x_183_) == 1)
{
lean_object* v_fvarId_188_; lean_object* v_fvarId_189_; uint8_t v___x_190_; 
v_fvarId_188_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_fvarId_188_);
lean_dec_ref(v_x_182_);
v_fvarId_189_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_fvarId_189_);
lean_dec_ref(v_x_183_);
v___x_190_ = l_Lean_instBEqFVarId_beq(v_fvarId_188_, v_fvarId_189_);
lean_dec(v_fvarId_189_);
lean_dec(v_fvarId_188_);
return v___x_190_;
}
else
{
uint8_t v___x_191_; 
lean_dec_ref(v_x_182_);
lean_dec_ref(v_x_183_);
v___x_191_ = 0;
return v___x_191_;
}
}
default: 
{
if (lean_obj_tag(v_x_183_) == 2)
{
lean_object* v_id_192_; lean_object* v_ref_193_; lean_object* v_proof_194_; lean_object* v_id_195_; lean_object* v_ref_196_; lean_object* v_proof_197_; uint8_t v___x_198_; 
v_id_192_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_id_192_);
v_ref_193_ = lean_ctor_get(v_x_182_, 1);
lean_inc(v_ref_193_);
v_proof_194_ = lean_ctor_get(v_x_182_, 2);
lean_inc_ref(v_proof_194_);
lean_dec_ref(v_x_182_);
v_id_195_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_id_195_);
v_ref_196_ = lean_ctor_get(v_x_183_, 1);
lean_inc(v_ref_196_);
v_proof_197_ = lean_ctor_get(v_x_183_, 2);
lean_inc_ref(v_proof_197_);
lean_dec_ref(v_x_183_);
v___x_198_ = lean_name_eq(v_id_192_, v_id_195_);
lean_dec(v_id_195_);
lean_dec(v_id_192_);
if (v___x_198_ == 0)
{
lean_dec_ref(v_proof_197_);
lean_dec(v_ref_196_);
lean_dec_ref(v_proof_194_);
lean_dec(v_ref_193_);
return v___x_198_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = l_Lean_Syntax_structEq(v_ref_193_, v_ref_196_);
if (v___x_199_ == 0)
{
lean_dec_ref(v_proof_197_);
lean_dec_ref(v_proof_194_);
return v___x_199_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = lean_expr_eqv(v_proof_194_, v_proof_197_);
lean_dec_ref(v_proof_197_);
lean_dec_ref(v_proof_194_);
return v___x_200_;
}
}
}
else
{
uint8_t v___x_201_; 
lean_dec_ref(v_x_182_);
lean_dec_ref(v_x_183_);
v___x_201_ = 0;
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq___boxed(lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_202_, v_x_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(lean_object* v_x_208_){
_start:
{
lean_object* v_declName_209_; 
v_declName_209_ = lean_ctor_get(v_x_208_, 0);
lean_inc(v_declName_209_);
return v_declName_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key___boxed(lean_object* v_x_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(v_x_210_);
lean_dec_ref(v_x_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
if (lean_obj_tag(v_a_212_) == 0)
{
lean_object* v___x_214_; 
v___x_214_ = l_List_reverse___redArg(v_a_213_);
return v___x_214_;
}
else
{
lean_object* v_head_215_; lean_object* v_tail_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_225_; 
v_head_215_ = lean_ctor_get(v_a_212_, 0);
v_tail_216_ = lean_ctor_get(v_a_212_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v_a_212_);
if (v_isSharedCheck_225_ == 0)
{
v___x_218_ = v_a_212_;
v_isShared_219_ = v_isSharedCheck_225_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_tail_216_);
lean_inc(v_head_215_);
lean_dec(v_a_212_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_225_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = l_Lean_mkLevelParam(v_head_215_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v_a_213_);
lean_ctor_set(v___x_218_, 0, v___x_220_);
v___x_222_ = v___x_218_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_a_213_);
v___x_222_ = v_reuseFailAlloc_224_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
v_a_212_ = v_tail_216_;
v_a_213_ = v___x_222_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v___x_232_; lean_object* v_env_233_; lean_object* v___x_234_; lean_object* v_mctx_235_; lean_object* v_lctx_236_; lean_object* v_options_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_232_ = lean_st_ref_get(v___y_230_);
v_env_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc_ref(v_env_233_);
lean_dec(v___x_232_);
v___x_234_ = lean_st_ref_get(v___y_228_);
v_mctx_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_ref(v_mctx_235_);
lean_dec(v___x_234_);
v_lctx_236_ = lean_ctor_get(v___y_227_, 2);
v_options_237_ = lean_ctor_get(v___y_229_, 2);
lean_inc_ref(v_options_237_);
lean_inc_ref(v_lctx_236_);
v___x_238_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_238_, 0, v_env_233_);
lean_ctor_set(v___x_238_, 1, v_mctx_235_);
lean_ctor_set(v___x_238_, 2, v_lctx_236_);
lean_ctor_set(v___x_238_, 3, v_options_237_);
v___x_239_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_msgData_226_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msgData_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_ref_254_; lean_object* v___x_255_; lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_264_; 
v_ref_254_ = lean_ctor_get(v___y_251_, 5);
v___x_255_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_264_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
lean_inc(v_ref_254_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v_ref_254_);
lean_ctor_set(v___x_260_, 1, v_a_256_);
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 1);
lean_ctor_set(v___x_258_, 0, v___x_260_);
v___x_262_ = v___x_258_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_272_, lean_object* v_msg_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_fileName_279_; lean_object* v_fileMap_280_; lean_object* v_options_281_; lean_object* v_currRecDepth_282_; lean_object* v_maxRecDepth_283_; lean_object* v_ref_284_; lean_object* v_currNamespace_285_; lean_object* v_openDecls_286_; lean_object* v_initHeartbeats_287_; lean_object* v_maxHeartbeats_288_; lean_object* v_quotContext_289_; lean_object* v_currMacroScope_290_; uint8_t v_diag_291_; lean_object* v_cancelTk_x3f_292_; uint8_t v_suppressElabErrors_293_; lean_object* v_inheritedTraceOptions_294_; lean_object* v_ref_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_fileName_279_ = lean_ctor_get(v___y_276_, 0);
v_fileMap_280_ = lean_ctor_get(v___y_276_, 1);
v_options_281_ = lean_ctor_get(v___y_276_, 2);
v_currRecDepth_282_ = lean_ctor_get(v___y_276_, 3);
v_maxRecDepth_283_ = lean_ctor_get(v___y_276_, 4);
v_ref_284_ = lean_ctor_get(v___y_276_, 5);
v_currNamespace_285_ = lean_ctor_get(v___y_276_, 6);
v_openDecls_286_ = lean_ctor_get(v___y_276_, 7);
v_initHeartbeats_287_ = lean_ctor_get(v___y_276_, 8);
v_maxHeartbeats_288_ = lean_ctor_get(v___y_276_, 9);
v_quotContext_289_ = lean_ctor_get(v___y_276_, 10);
v_currMacroScope_290_ = lean_ctor_get(v___y_276_, 11);
v_diag_291_ = lean_ctor_get_uint8(v___y_276_, sizeof(void*)*14);
v_cancelTk_x3f_292_ = lean_ctor_get(v___y_276_, 12);
v_suppressElabErrors_293_ = lean_ctor_get_uint8(v___y_276_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_294_ = lean_ctor_get(v___y_276_, 13);
v_ref_295_ = l_Lean_replaceRef(v_ref_272_, v_ref_284_);
lean_inc_ref(v_inheritedTraceOptions_294_);
lean_inc(v_cancelTk_x3f_292_);
lean_inc(v_currMacroScope_290_);
lean_inc(v_quotContext_289_);
lean_inc(v_maxHeartbeats_288_);
lean_inc(v_initHeartbeats_287_);
lean_inc(v_openDecls_286_);
lean_inc(v_currNamespace_285_);
lean_inc(v_maxRecDepth_283_);
lean_inc(v_currRecDepth_282_);
lean_inc_ref(v_options_281_);
lean_inc_ref(v_fileMap_280_);
lean_inc_ref(v_fileName_279_);
v___x_296_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_296_, 0, v_fileName_279_);
lean_ctor_set(v___x_296_, 1, v_fileMap_280_);
lean_ctor_set(v___x_296_, 2, v_options_281_);
lean_ctor_set(v___x_296_, 3, v_currRecDepth_282_);
lean_ctor_set(v___x_296_, 4, v_maxRecDepth_283_);
lean_ctor_set(v___x_296_, 5, v_ref_295_);
lean_ctor_set(v___x_296_, 6, v_currNamespace_285_);
lean_ctor_set(v___x_296_, 7, v_openDecls_286_);
lean_ctor_set(v___x_296_, 8, v_initHeartbeats_287_);
lean_ctor_set(v___x_296_, 9, v_maxHeartbeats_288_);
lean_ctor_set(v___x_296_, 10, v_quotContext_289_);
lean_ctor_set(v___x_296_, 11, v_currMacroScope_290_);
lean_ctor_set(v___x_296_, 12, v_cancelTk_x3f_292_);
lean_ctor_set(v___x_296_, 13, v_inheritedTraceOptions_294_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*14, v_diag_291_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*14 + 1, v_suppressElabErrors_293_);
v___x_297_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_273_, v___y_274_, v___y_275_, v___x_296_, v___y_277_);
lean_dec_ref(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_298_, lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_298_, v_msg_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v_ref_298_);
return v_res_305_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_306_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
lean_ctor_set(v___x_311_, 3, v___x_310_);
lean_ctor_set(v___x_311_, 4, v___x_309_);
lean_ctor_set(v___x_311_, 5, v___x_309_);
lean_ctor_set(v___x_311_, 6, v___x_309_);
lean_ctor_set(v___x_311_, 7, v___x_309_);
lean_ctor_set(v___x_311_, 8, v___x_309_);
lean_ctor_set(v___x_311_, 9, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_unsigned_to_nat(32u);
v___x_313_ = lean_mk_empty_array_with_capacity(v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_315_ = ((size_t)5ULL);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_unsigned_to_nat(32u);
v___x_318_ = lean_mk_empty_array_with_capacity(v___x_317_);
v___x_319_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_320_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
lean_ctor_set(v___x_320_, 2, v___x_316_);
lean_ctor_set(v___x_320_, 3, v___x_316_);
lean_ctor_set_usize(v___x_320_, 4, v___x_315_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_321_ = lean_box(1);
v___x_322_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_323_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
lean_ctor_set(v___x_324_, 2, v___x_321_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_327_ = l_Lean_stringToMessageData(v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_330_ = l_Lean_stringToMessageData(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_336_ = l_Lean_stringToMessageData(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_339_ = l_Lean_stringToMessageData(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_346_, lean_object* v_declHint_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; lean_object* v_env_351_; uint8_t v___x_352_; 
v___x_350_ = lean_st_ref_get(v___y_348_);
v_env_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_env_351_);
lean_dec(v___x_350_);
v___x_352_ = l_Lean_Name_isAnonymous(v_declHint_347_);
if (v___x_352_ == 0)
{
uint8_t v_isExporting_353_; 
v_isExporting_353_ = lean_ctor_get_uint8(v_env_351_, sizeof(void*)*8);
if (v_isExporting_353_ == 0)
{
lean_object* v___x_354_; 
lean_dec_ref(v_env_351_);
lean_dec(v_declHint_347_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v_msg_346_);
return v___x_354_;
}
else
{
lean_object* v___x_355_; uint8_t v___x_356_; 
lean_inc_ref(v_env_351_);
v___x_355_ = l_Lean_Environment_setExporting(v_env_351_, v___x_352_);
lean_inc(v_declHint_347_);
lean_inc_ref(v___x_355_);
v___x_356_ = l_Lean_Environment_contains(v___x_355_, v_declHint_347_, v_isExporting_353_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
lean_dec_ref(v___x_355_);
lean_dec_ref(v_env_351_);
lean_dec(v_declHint_347_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v_msg_346_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_c_363_; lean_object* v___x_364_; 
v___x_358_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_359_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_360_ = l_Lean_Options_empty;
v___x_361_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_361_, 0, v___x_355_);
lean_ctor_set(v___x_361_, 1, v___x_358_);
lean_ctor_set(v___x_361_, 2, v___x_359_);
lean_ctor_set(v___x_361_, 3, v___x_360_);
lean_inc(v_declHint_347_);
v___x_362_ = l_Lean_MessageData_ofConstName(v_declHint_347_, v___x_352_);
v_c_363_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_363_, 0, v___x_361_);
lean_ctor_set(v_c_363_, 1, v___x_362_);
v___x_364_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_351_, v_declHint_347_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec_ref(v_env_351_);
lean_dec(v_declHint_347_);
v___x_365_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_c_363_);
v___x_367_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = l_Lean_MessageData_note(v___x_368_);
v___x_370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_370_, 0, v_msg_346_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
else
{
lean_object* v_val_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_407_; 
v_val_372_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_407_ == 0)
{
v___x_374_ = v___x_364_;
v_isShared_375_ = v_isSharedCheck_407_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_val_372_);
lean_dec(v___x_364_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_407_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_mod_379_; uint8_t v___x_380_; 
v___x_376_ = lean_box(0);
v___x_377_ = l_Lean_Environment_header(v_env_351_);
lean_dec_ref(v_env_351_);
v___x_378_ = l_Lean_EnvironmentHeader_moduleNames(v___x_377_);
v_mod_379_ = lean_array_get(v___x_376_, v___x_378_, v_val_372_);
lean_dec(v_val_372_);
lean_dec_ref(v___x_378_);
v___x_380_ = l_Lean_isPrivateName(v_declHint_347_);
lean_dec(v_declHint_347_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_381_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_c_363_);
v___x_383_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = l_Lean_MessageData_ofName(v_mod_379_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_MessageData_note(v___x_388_);
v___x_390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_390_, 0, v_msg_346_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
if (v_isShared_375_ == 0)
{
lean_ctor_set_tag(v___x_374_, 0);
lean_ctor_set(v___x_374_, 0, v___x_390_);
v___x_392_ = v___x_374_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_394_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_c_363_);
v___x_396_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_MessageData_ofName(v_mod_379_);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_Lean_MessageData_note(v___x_401_);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v_msg_346_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
if (v_isShared_375_ == 0)
{
lean_ctor_set_tag(v___x_374_, 0);
lean_ctor_set(v___x_374_, 0, v___x_403_);
v___x_405_ = v___x_374_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_408_; 
lean_dec_ref(v_env_351_);
lean_dec(v_declHint_347_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v_msg_346_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_409_, lean_object* v_declHint_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_409_, v_declHint_410_, v___y_411_);
lean_dec(v___y_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_414_, lean_object* v_declHint_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_431_; 
v___x_421_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_414_, v_declHint_415_, v___y_419_);
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_431_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_431_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_431_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_426_ = l_Lean_unknownIdentifierMessageTag;
v___x_427_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v_a_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_427_);
v___x_429_ = v___x_424_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_432_, lean_object* v_declHint_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_432_, v_declHint_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_440_, lean_object* v_msg_441_, lean_object* v_declHint_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; lean_object* v_a_449_; lean_object* v___x_450_; 
v___x_448_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_441_, v_declHint_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref(v___x_448_);
v___x_450_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_440_, v_a_449_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_451_, lean_object* v_msg_452_, lean_object* v_declHint_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_451_, v_msg_452_, v_declHint_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v_ref_451_);
return v_res_459_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_466_, lean_object* v_constName_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_473_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_474_ = 0;
lean_inc(v_constName_467_);
v___x_475_ = l_Lean_MessageData_ofConstName(v_constName_467_, v___x_474_);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_473_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_466_, v___x_478_, v_constName_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_480_, lean_object* v_constName_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_480_, v_constName_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v_ref_480_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(lean_object* v_constName_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_ref_494_; lean_object* v___x_495_; 
v_ref_494_ = lean_ctor_get(v___y_491_, 5);
v___x_495_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_494_, v_constName_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg___boxed(lean_object* v_constName_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(lean_object* v_constName_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; lean_object* v_env_510_; uint8_t v___x_511_; lean_object* v___x_512_; 
v___x_509_ = lean_st_ref_get(v___y_507_);
v_env_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc_ref(v_env_510_);
lean_dec(v___x_509_);
v___x_511_ = 0;
lean_inc(v_constName_503_);
v___x_512_ = l_Lean_Environment_find_x3f(v_env_510_, v_constName_503_, v___x_511_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
return v___x_513_;
}
else
{
lean_object* v_val_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_constName_503_);
v_val_514_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_512_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_val_514_);
lean_dec(v___x_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 0);
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_val_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0___boxed(lean_object* v_constName_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_constName_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(lean_object* v_x_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
switch(lean_obj_tag(v_x_529_))
{
case 0:
{
lean_object* v_declName_535_; lean_object* v___x_536_; 
v_declName_535_ = lean_ctor_get(v_x_529_, 0);
lean_inc_n(v_declName_535_, 2);
lean_dec_ref(v_x_529_);
v___x_536_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_535_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_549_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_549_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_549_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_549_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_541_ = l_Lean_ConstantInfo_levelParams(v_a_537_);
lean_dec(v_a_537_);
v___x_542_ = lean_box(0);
lean_inc(v___x_541_);
v___x_543_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_541_, v___x_542_);
v___x_544_ = l_Lean_mkConst(v_declName_535_, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_541_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_545_);
v___x_547_ = v___x_539_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_declName_535_);
v_a_550_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_536_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_536_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_568_; 
v_fvarId_558_ = lean_ctor_get(v_x_529_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_x_529_);
if (v_isSharedCheck_568_ == 0)
{
v___x_560_ = v_x_529_;
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_fvarId_558_);
lean_dec(v_x_529_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_562_ = lean_box(0);
v___x_563_ = l_Lean_mkFVar(v_fvarId_558_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 0);
lean_ctor_set(v___x_560_, 0, v___x_564_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
default: 
{
lean_object* v_proof_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_proof_569_ = lean_ctor_get(v_x_529_, 2);
lean_inc_ref(v_proof_569_);
lean_dec_ref(v_x_529_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_proof_569_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof___boxed(lean_object* v_x_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(v_x_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0(lean_object* v_00_u03b1_580_, lean_object* v_constName_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___boxed(lean_object* v_00_u03b1_588_, lean_object* v_constName_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0(v_00_u03b1_588_, v_constName_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_596_, lean_object* v_ref_597_, lean_object* v_constName_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_597_, v_constName_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_605_, lean_object* v_ref_606_, lean_object* v_constName_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1(v_00_u03b1_605_, v_ref_606_, v_constName_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v_ref_606_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_614_, lean_object* v_ref_615_, lean_object* v_msg_616_, lean_object* v_declHint_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_615_, v_msg_616_, v_declHint_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_624_, lean_object* v_ref_625_, lean_object* v_msg_626_, lean_object* v_declHint_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_624_, v_ref_625_, v_msg_626_, v_declHint_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v_ref_625_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_634_, lean_object* v_declHint_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_634_, v_declHint_635_, v___y_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_642_, lean_object* v_declHint_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_642_, v_declHint_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_650_, lean_object* v_ref_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_651_, v_msg_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_659_, lean_object* v_ref_660_, lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_659_, v_ref_660_, v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v_ref_660_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_668_, lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_676_, lean_object* v_msg_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(v_00_u03b1_676_, v_msg_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
return v_res_683_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0(void){
_start:
{
lean_object* v___x_684_; uint64_t v___x_685_; 
v___x_684_ = lean_unsigned_to_nat(1723u);
v___x_685_ = lean_uint64_of_nat(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT uint64_t l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0(lean_object* v_sp_686_){
_start:
{
lean_object* v___y_688_; lean_object* v_declName_691_; 
v_declName_691_ = lean_ctor_get(v_sp_686_, 0);
v___y_688_ = v_declName_691_;
goto v___jp_687_;
v___jp_687_:
{
if (lean_obj_tag(v___y_688_) == 0)
{
uint64_t v___x_689_; 
v___x_689_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
return v___x_689_;
}
else
{
uint64_t v_hash_690_; 
v_hash_690_ = lean_ctor_get_uint64(v___y_688_, sizeof(void*)*2);
return v_hash_690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___boxed(lean_object* v_sp_692_){
_start:
{
uint64_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0(v_sp_692_);
lean_dec_ref(v_sp_692_);
v_r_694_ = lean_box_uint64(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(lean_object* v_e_697_, lean_object* v___y_698_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = l_Lean_Expr_hasMVar(v_e_697_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v_e_697_);
return v___x_701_;
}
else
{
lean_object* v___x_702_; lean_object* v_mctx_703_; lean_object* v___x_704_; lean_object* v_fst_705_; lean_object* v_snd_706_; lean_object* v___x_707_; lean_object* v_cache_708_; lean_object* v_zetaDeltaFVarIds_709_; lean_object* v_postponed_710_; lean_object* v_diag_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_720_; 
v___x_702_ = lean_st_ref_get(v___y_698_);
v_mctx_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc_ref(v_mctx_703_);
lean_dec(v___x_702_);
v___x_704_ = l_Lean_instantiateMVarsCore(v_mctx_703_, v_e_697_);
v_fst_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_fst_705_);
v_snd_706_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_snd_706_);
lean_dec_ref(v___x_704_);
v___x_707_ = lean_st_ref_take(v___y_698_);
v_cache_708_ = lean_ctor_get(v___x_707_, 1);
v_zetaDeltaFVarIds_709_ = lean_ctor_get(v___x_707_, 2);
v_postponed_710_ = lean_ctor_get(v___x_707_, 3);
v_diag_711_ = lean_ctor_get(v___x_707_, 4);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v___x_707_, 0);
lean_dec(v_unused_721_);
v___x_713_ = v___x_707_;
v_isShared_714_ = v_isSharedCheck_720_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_diag_711_);
lean_inc(v_postponed_710_);
lean_inc(v_zetaDeltaFVarIds_709_);
lean_inc(v_cache_708_);
lean_dec(v___x_707_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_720_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v_snd_706_);
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_snd_706_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_cache_708_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_zetaDeltaFVarIds_709_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_postponed_710_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_diag_711_);
v___x_716_ = v_reuseFailAlloc_719_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_st_ref_set(v___y_698_, v___x_716_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_fst_705_);
return v___x_718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg___boxed(lean_object* v_e_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_e_722_, v___y_723_);
lean_dec(v___y_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0(lean_object* v_e_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_e_726_, v___y_728_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___boxed(lean_object* v_e_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0(v_e_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(lean_object* v_proof_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_prf_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; 
switch(lean_obj_tag(v_proof_740_))
{
case 0:
{
lean_object* v_declName_802_; lean_object* v___x_803_; 
v_declName_802_ = lean_ctor_get(v_proof_740_, 0);
lean_inc(v_declName_802_);
lean_dec_ref(v_proof_740_);
v___x_803_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_802_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___x_803_);
v_prf_747_ = v_a_804_;
v___y_748_ = v_a_741_;
v___y_749_ = v_a_742_;
v___y_750_ = v_a_743_;
v___y_751_ = v_a_744_;
goto v___jp_746_;
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
v_a_805_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_803_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_803_);
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
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
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
}
case 1:
{
lean_object* v_fvarId_813_; lean_object* v___x_814_; 
v_fvarId_813_ = lean_ctor_get(v_proof_740_, 0);
lean_inc(v_fvarId_813_);
lean_dec_ref(v_proof_740_);
v___x_814_ = l_Lean_mkFVar(v_fvarId_813_);
v_prf_747_ = v___x_814_;
v___y_748_ = v_a_741_;
v___y_749_ = v_a_742_;
v___y_750_ = v_a_743_;
v___y_751_ = v_a_744_;
goto v___jp_746_;
}
default: 
{
lean_object* v_proof_815_; 
v_proof_815_ = lean_ctor_get(v_proof_740_, 2);
lean_inc_ref(v_proof_815_);
lean_dec_ref(v_proof_740_);
v_prf_747_ = v_proof_815_;
v___y_748_ = v_a_741_;
v___y_749_ = v_a_742_;
v___y_750_ = v_a_743_;
v___y_751_ = v_a_744_;
goto v___jp_746_;
}
}
v___jp_746_:
{
lean_object* v___x_752_; 
lean_inc(v___y_751_);
lean_inc_ref(v___y_750_);
lean_inc(v___y_749_);
lean_inc_ref(v___y_748_);
lean_inc_ref(v_prf_747_);
v___x_752_ = lean_infer_type(v_prf_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v_a_755_; uint8_t v___x_756_; lean_object* v___x_757_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref(v___x_752_);
v___x_754_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_a_753_, v___y_749_);
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref(v___x_754_);
v___x_756_ = 0;
v___x_757_ = l_Lean_Meta_forallMetaTelescope(v_a_755_, v___x_756_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_785_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_785_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_785_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_785_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_snd_762_; lean_object* v_fst_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_784_; 
v_snd_762_ = lean_ctor_get(v_a_758_, 1);
v_fst_763_ = lean_ctor_get(v_a_758_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v_a_758_);
if (v_isSharedCheck_784_ == 0)
{
v___x_765_ = v_a_758_;
v_isShared_766_ = v_isSharedCheck_784_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_snd_762_);
lean_inc(v_fst_763_);
lean_dec(v_a_758_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_784_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v_fst_767_; lean_object* v_snd_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_783_; 
v_fst_767_ = lean_ctor_get(v_snd_762_, 0);
v_snd_768_ = lean_ctor_get(v_snd_762_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_snd_762_);
if (v_isSharedCheck_783_ == 0)
{
v___x_770_ = v_snd_762_;
v_isShared_771_ = v_isSharedCheck_783_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_snd_768_);
lean_inc(v_fst_767_);
lean_dec(v_snd_762_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_783_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_774_; 
lean_inc(v_fst_763_);
v___x_772_ = l_Lean_Expr_beta(v_prf_747_, v_fst_763_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_772_);
v___x_774_ = v___x_770_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_snd_768_);
v___x_774_ = v_reuseFailAlloc_782_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___x_774_);
lean_ctor_set(v___x_765_, 0, v_fst_767_);
v___x_776_ = v___x_765_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_fst_767_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_781_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_fst_763_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_777_);
v___x_779_ = v___x_760_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_prf_747_);
v_a_786_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_757_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_757_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v_prf_747_);
v_a_794_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_752_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_752_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate___boxed(lean_object* v_proof_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(v_proof_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
return v_res_822_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4));
v___x_831_ = l_Lean_stringToMessageData(v___x_830_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6));
v___x_834_ = l_Lean_stringToMessageData(v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0(lean_object* v_x_835_){
_start:
{
switch(lean_obj_tag(v_x_835_))
{
case 0:
{
lean_object* v_declName_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_declName_836_ = lean_ctor_get(v_x_835_, 0);
lean_inc(v_declName_836_);
lean_dec_ref(v_x_835_);
v___x_837_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1);
v___x_838_ = l_Lean_MessageData_ofName(v_declName_836_);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
return v___x_839_;
}
case 1:
{
lean_object* v_fvarId_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_fvarId_840_ = lean_ctor_get(v_x_835_, 0);
lean_inc(v_fvarId_840_);
lean_dec_ref(v_x_835_);
v___x_841_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3);
v___x_842_ = l_Lean_mkFVar(v_fvarId_840_);
v___x_843_ = l_Lean_MessageData_ofExpr(v___x_842_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_841_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
return v___x_844_;
}
default: 
{
lean_object* v_ref_845_; lean_object* v_proof_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_ref_845_ = lean_ctor_get(v_x_835_, 1);
lean_inc(v_ref_845_);
v_proof_846_ = lean_ctor_get(v_x_835_, 2);
lean_inc_ref(v_proof_846_);
lean_dec_ref(v_x_835_);
v___x_847_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5);
v___x_848_ = l_Lean_MessageData_ofSyntax(v_ref_845_);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_MessageData_ofExpr(v_proof_846_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
return v___x_853_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = lean_box(0);
v___x_862_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2));
v___x_863_ = l_Lean_Expr_const___override(v___x_862_, v___x_861_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_864_ = lean_unsigned_to_nat(1000u);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default));
v___x_867_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3);
v___x_868_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0));
v___x_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
lean_ctor_set(v___x_869_, 2, v___x_866_);
lean_ctor_set(v___x_869_, 3, v___x_865_);
lean_ctor_set(v___x_869_, 4, v___x_864_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default(void){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem(void){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default;
return v___x_871_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(lean_object* v_xs_872_, lean_object* v_ys_873_, lean_object* v_x_874_){
_start:
{
lean_object* v_zero_875_; uint8_t v_isZero_876_; 
v_zero_875_ = lean_unsigned_to_nat(0u);
v_isZero_876_ = lean_nat_dec_eq(v_x_874_, v_zero_875_);
if (v_isZero_876_ == 1)
{
lean_dec(v_x_874_);
return v_isZero_876_;
}
else
{
lean_object* v_one_877_; lean_object* v_n_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_one_877_ = lean_unsigned_to_nat(1u);
v_n_878_ = lean_nat_sub(v_x_874_, v_one_877_);
lean_dec(v_x_874_);
v___x_879_ = lean_array_fget_borrowed(v_xs_872_, v_n_878_);
v___x_880_ = lean_array_fget_borrowed(v_ys_873_, v_n_878_);
v___x_881_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_dec(v_n_878_);
return v___x_881_;
}
else
{
v_x_874_ = v_n_878_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg___boxed(lean_object* v_xs_883_, lean_object* v_ys_884_, lean_object* v_x_885_){
_start:
{
uint8_t v_res_886_; lean_object* v_r_887_; 
v_res_886_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_xs_883_, v_ys_884_, v_x_885_);
lean_dec_ref(v_ys_884_);
lean_dec_ref(v_xs_883_);
v_r_887_ = lean_box(v_res_886_);
return v_r_887_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
lean_object* v_keys_890_; lean_object* v_prog_891_; lean_object* v_proof_892_; lean_object* v_etaPotential_893_; lean_object* v_priority_894_; lean_object* v_keys_895_; lean_object* v_prog_896_; lean_object* v_proof_897_; lean_object* v_etaPotential_898_; lean_object* v_priority_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_keys_890_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_keys_890_);
v_prog_891_ = lean_ctor_get(v_x_888_, 1);
lean_inc_ref(v_prog_891_);
v_proof_892_ = lean_ctor_get(v_x_888_, 2);
lean_inc_ref(v_proof_892_);
v_etaPotential_893_ = lean_ctor_get(v_x_888_, 3);
lean_inc(v_etaPotential_893_);
v_priority_894_ = lean_ctor_get(v_x_888_, 4);
lean_inc(v_priority_894_);
lean_dec_ref(v_x_888_);
v_keys_895_ = lean_ctor_get(v_x_889_, 0);
lean_inc_ref(v_keys_895_);
v_prog_896_ = lean_ctor_get(v_x_889_, 1);
lean_inc_ref(v_prog_896_);
v_proof_897_ = lean_ctor_get(v_x_889_, 2);
lean_inc_ref(v_proof_897_);
v_etaPotential_898_ = lean_ctor_get(v_x_889_, 3);
lean_inc(v_etaPotential_898_);
v_priority_899_ = lean_ctor_get(v_x_889_, 4);
lean_inc(v_priority_899_);
lean_dec_ref(v_x_889_);
v___x_900_ = lean_array_get_size(v_keys_890_);
v___x_901_ = lean_array_get_size(v_keys_895_);
v___x_902_ = lean_nat_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_dec(v_priority_899_);
lean_dec(v_etaPotential_898_);
lean_dec_ref(v_proof_897_);
lean_dec_ref(v_prog_896_);
lean_dec_ref(v_keys_895_);
lean_dec(v_priority_894_);
lean_dec(v_etaPotential_893_);
lean_dec_ref(v_proof_892_);
lean_dec_ref(v_prog_891_);
lean_dec_ref(v_keys_890_);
return v___x_902_;
}
else
{
uint8_t v___x_903_; 
v___x_903_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_keys_890_, v_keys_895_, v___x_900_);
lean_dec_ref(v_keys_895_);
lean_dec_ref(v_keys_890_);
if (v___x_903_ == 0)
{
lean_dec(v_priority_899_);
lean_dec(v_etaPotential_898_);
lean_dec_ref(v_proof_897_);
lean_dec_ref(v_prog_896_);
lean_dec(v_priority_894_);
lean_dec(v_etaPotential_893_);
lean_dec_ref(v_proof_892_);
lean_dec_ref(v_prog_891_);
return v___x_903_;
}
else
{
uint8_t v___x_904_; 
v___x_904_ = lean_expr_eqv(v_prog_891_, v_prog_896_);
lean_dec_ref(v_prog_896_);
lean_dec_ref(v_prog_891_);
if (v___x_904_ == 0)
{
lean_dec(v_priority_899_);
lean_dec(v_etaPotential_898_);
lean_dec_ref(v_proof_897_);
lean_dec(v_priority_894_);
lean_dec(v_etaPotential_893_);
lean_dec_ref(v_proof_892_);
return v___x_904_;
}
else
{
uint8_t v___x_905_; 
v___x_905_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_proof_892_, v_proof_897_);
if (v___x_905_ == 0)
{
lean_dec(v_priority_899_);
lean_dec(v_etaPotential_898_);
lean_dec(v_priority_894_);
lean_dec(v_etaPotential_893_);
return v___x_905_;
}
else
{
uint8_t v___x_906_; 
v___x_906_ = lean_nat_dec_eq(v_etaPotential_893_, v_etaPotential_898_);
lean_dec(v_etaPotential_898_);
lean_dec(v_etaPotential_893_);
if (v___x_906_ == 0)
{
lean_dec(v_priority_899_);
lean_dec(v_priority_894_);
return v___x_906_;
}
else
{
uint8_t v___x_907_; 
v___x_907_ = lean_nat_dec_eq(v_priority_894_, v_priority_899_);
lean_dec(v_priority_899_);
lean_dec(v_priority_894_);
return v___x_907_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq___boxed(lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
uint8_t v_res_910_; lean_object* v_r_911_; 
v_res_910_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(v_x_908_, v_x_909_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(lean_object* v_xs_912_, lean_object* v_ys_913_, lean_object* v_hsz_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
uint8_t v___x_917_; 
v___x_917_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_xs_912_, v_ys_913_, v_x_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___boxed(lean_object* v_xs_918_, lean_object* v_ys_919_, lean_object* v_hsz_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(v_xs_918_, v_ys_919_, v_hsz_920_, v_x_921_, v_x_922_);
lean_dec_ref(v_ys_919_);
lean_dec_ref(v_xs_918_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_927_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(lean_object* v_00_u03b2_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(lean_box(0));
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1);
v___x_935_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default(void){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems(void){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
lean_object* v_ks_943_; lean_object* v_vs_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_968_; 
v_ks_943_ = lean_ctor_get(v_x_939_, 0);
v_vs_944_ = lean_ctor_get(v_x_939_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_x_939_);
if (v_isSharedCheck_968_ == 0)
{
v___x_946_ = v_x_939_;
v_isShared_947_ = v_isSharedCheck_968_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_vs_944_);
lean_inc(v_ks_943_);
lean_dec(v_x_939_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_968_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_array_get_size(v_ks_943_);
v___x_949_ = lean_nat_dec_lt(v_x_940_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec(v_x_940_);
v___x_950_ = lean_array_push(v_ks_943_, v_x_941_);
v___x_951_ = lean_array_push(v_vs_944_, v_x_942_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_951_);
lean_ctor_set(v___x_946_, 0, v___x_950_);
v___x_953_ = v___x_946_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v_k_x27_955_; uint8_t v___x_956_; 
v_k_x27_955_ = lean_array_fget_borrowed(v_ks_943_, v_x_940_);
v___x_956_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_941_, v_k_x27_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_958_; 
if (v_isShared_947_ == 0)
{
v___x_958_ = v___x_946_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_ks_943_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_vs_944_);
v___x_958_ = v_reuseFailAlloc_962_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_nat_add(v_x_940_, v___x_959_);
lean_dec(v_x_940_);
v_x_939_ = v___x_958_;
v_x_940_ = v___x_960_;
goto _start;
}
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_963_ = lean_array_fset(v_ks_943_, v_x_940_, v_x_941_);
v___x_964_ = lean_array_fset(v_vs_944_, v_x_940_, v_x_942_);
lean_dec(v_x_940_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_964_);
lean_ctor_set(v___x_946_, 0, v___x_963_);
v___x_966_ = v___x_946_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_n_969_, lean_object* v_k_970_, lean_object* v_v_971_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_n_969_, v___x_972_, v_k_970_, v_v_971_);
return v___x_973_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_974_; size_t v___x_975_; size_t v___x_976_; 
v___x_974_ = ((size_t)5ULL);
v___x_975_ = ((size_t)1ULL);
v___x_976_ = lean_usize_shift_left(v___x_975_, v___x_974_);
return v___x_976_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_977_; size_t v___x_978_; size_t v___x_979_; 
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_979_ = lean_usize_sub(v___x_978_, v___x_977_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(lean_object* v_x_981_, size_t v_x_982_, size_t v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
if (lean_obj_tag(v_x_981_) == 0)
{
lean_object* v_es_986_; size_t v___x_987_; size_t v___x_988_; size_t v___x_989_; size_t v___x_990_; lean_object* v_j_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v_es_986_ = lean_ctor_get(v_x_981_, 0);
v___x_987_ = ((size_t)5ULL);
v___x_988_ = ((size_t)1ULL);
v___x_989_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_990_ = lean_usize_land(v_x_982_, v___x_989_);
v_j_991_ = lean_usize_to_nat(v___x_990_);
v___x_992_ = lean_array_get_size(v_es_986_);
v___x_993_ = lean_nat_dec_lt(v_j_991_, v___x_992_);
if (v___x_993_ == 0)
{
lean_dec(v_j_991_);
lean_dec(v_x_985_);
lean_dec(v_x_984_);
return v_x_981_;
}
else
{
lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1030_; 
lean_inc_ref(v_es_986_);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_x_981_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; 
v_unused_1031_ = lean_ctor_get(v_x_981_, 0);
lean_dec(v_unused_1031_);
v___x_995_ = v_x_981_;
v_isShared_996_ = v_isSharedCheck_1030_;
goto v_resetjp_994_;
}
else
{
lean_dec(v_x_981_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1030_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_v_997_; lean_object* v___x_998_; lean_object* v_xs_x27_999_; lean_object* v___y_1001_; 
v_v_997_ = lean_array_fget(v_es_986_, v_j_991_);
v___x_998_ = lean_box(0);
v_xs_x27_999_ = lean_array_fset(v_es_986_, v_j_991_, v___x_998_);
switch(lean_obj_tag(v_v_997_))
{
case 0:
{
lean_object* v_key_1006_; lean_object* v_val_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1017_; 
v_key_1006_ = lean_ctor_get(v_v_997_, 0);
v_val_1007_ = lean_ctor_get(v_v_997_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_v_997_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1009_ = v_v_997_;
v_isShared_1010_ = v_isSharedCheck_1017_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_val_1007_);
lean_inc(v_key_1006_);
lean_dec(v_v_997_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1017_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_984_, v_key_1006_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_del_object(v___x_1009_);
v___x_1012_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1006_, v_val_1007_, v_x_984_, v_x_985_);
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
v___y_1001_ = v___x_1013_;
goto v___jp_1000_;
}
else
{
lean_object* v___x_1015_; 
lean_dec(v_val_1007_);
lean_dec(v_key_1006_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v_x_985_);
lean_ctor_set(v___x_1009_, 0, v_x_984_);
v___x_1015_ = v___x_1009_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_x_984_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_x_985_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
v___y_1001_ = v___x_1015_;
goto v___jp_1000_;
}
}
}
}
case 1:
{
lean_object* v_node_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1028_; 
v_node_1018_ = lean_ctor_get(v_v_997_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_v_997_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1020_ = v_v_997_;
v_isShared_1021_ = v_isSharedCheck_1028_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_node_1018_);
lean_dec(v_v_997_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1028_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1022_ = lean_usize_shift_right(v_x_982_, v___x_987_);
v___x_1023_ = lean_usize_add(v_x_983_, v___x_988_);
v___x_1024_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_node_1018_, v___x_1022_, v___x_1023_, v_x_984_, v_x_985_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1024_);
v___x_1026_ = v___x_1020_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
v___y_1001_ = v___x_1026_;
goto v___jp_1000_;
}
}
}
default: 
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_x_984_);
lean_ctor_set(v___x_1029_, 1, v_x_985_);
v___y_1001_ = v___x_1029_;
goto v___jp_1000_;
}
}
v___jp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = lean_array_fset(v_xs_x27_999_, v_j_991_, v___y_1001_);
lean_dec(v_j_991_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1002_);
v___x_1004_ = v___x_995_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
else
{
lean_object* v_ks_1032_; lean_object* v_vs_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1053_; 
v_ks_1032_ = lean_ctor_get(v_x_981_, 0);
v_vs_1033_ = lean_ctor_get(v_x_981_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_x_981_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1035_ = v_x_981_;
v_isShared_1036_ = v_isSharedCheck_1053_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_vs_1033_);
lean_inc(v_ks_1032_);
lean_dec(v_x_981_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1053_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_ks_1032_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_vs_1033_);
v___x_1038_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v_newNode_1039_; uint8_t v___y_1041_; size_t v___x_1047_; uint8_t v___x_1048_; 
v_newNode_1039_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(v___x_1038_, v_x_984_, v_x_985_);
v___x_1047_ = ((size_t)7ULL);
v___x_1048_ = lean_usize_dec_le(v___x_1047_, v_x_983_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1049_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1039_);
v___x_1050_ = lean_unsigned_to_nat(4u);
v___x_1051_ = lean_nat_dec_lt(v___x_1049_, v___x_1050_);
lean_dec(v___x_1049_);
v___y_1041_ = v___x_1051_;
goto v___jp_1040_;
}
else
{
v___y_1041_ = v___x_1048_;
goto v___jp_1040_;
}
v___jp_1040_:
{
if (v___y_1041_ == 0)
{
lean_object* v_ks_1042_; lean_object* v_vs_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_ks_1042_ = lean_ctor_get(v_newNode_1039_, 0);
lean_inc_ref(v_ks_1042_);
v_vs_1043_ = lean_ctor_get(v_newNode_1039_, 1);
lean_inc_ref(v_vs_1043_);
lean_dec_ref(v_newNode_1039_);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2);
v___x_1046_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_x_983_, v_ks_1042_, v_vs_1043_, v___x_1044_, v___x_1045_);
lean_dec_ref(v_vs_1043_);
lean_dec_ref(v_ks_1042_);
return v___x_1046_;
}
else
{
return v_newNode_1039_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(size_t v_depth_1054_, lean_object* v_keys_1055_, lean_object* v_vals_1056_, lean_object* v_i_1057_, lean_object* v_entries_1058_){
_start:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = lean_array_get_size(v_keys_1055_);
v___x_1060_ = lean_nat_dec_lt(v_i_1057_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_dec(v_i_1057_);
return v_entries_1058_;
}
else
{
lean_object* v_k_1061_; lean_object* v_v_1062_; uint64_t v___x_1063_; size_t v_h_1064_; size_t v___x_1065_; lean_object* v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; size_t v_h_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_k_1061_ = lean_array_fget_borrowed(v_keys_1055_, v_i_1057_);
v_v_1062_ = lean_array_fget_borrowed(v_vals_1056_, v_i_1057_);
v___x_1063_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1061_);
v_h_1064_ = lean_uint64_to_usize(v___x_1063_);
v___x_1065_ = ((size_t)5ULL);
v___x_1066_ = lean_unsigned_to_nat(1u);
v___x_1067_ = ((size_t)1ULL);
v___x_1068_ = lean_usize_sub(v_depth_1054_, v___x_1067_);
v___x_1069_ = lean_usize_mul(v___x_1065_, v___x_1068_);
v_h_1070_ = lean_usize_shift_right(v_h_1064_, v___x_1069_);
v___x_1071_ = lean_nat_add(v_i_1057_, v___x_1066_);
lean_dec(v_i_1057_);
lean_inc(v_v_1062_);
lean_inc(v_k_1061_);
v___x_1072_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_entries_1058_, v_h_1070_, v_depth_1054_, v_k_1061_, v_v_1062_);
v_i_1057_ = v___x_1071_;
v_entries_1058_ = v___x_1072_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_1074_, lean_object* v_keys_1075_, lean_object* v_vals_1076_, lean_object* v_i_1077_, lean_object* v_entries_1078_){
_start:
{
size_t v_depth_boxed_1079_; lean_object* v_res_1080_; 
v_depth_boxed_1079_ = lean_unbox_usize(v_depth_1074_);
lean_dec(v_depth_1074_);
v_res_1080_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_1079_, v_keys_1075_, v_vals_1076_, v_i_1077_, v_entries_1078_);
lean_dec_ref(v_vals_1076_);
lean_dec_ref(v_keys_1075_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
size_t v_x_1605__boxed_1086_; size_t v_x_1606__boxed_1087_; lean_object* v_res_1088_; 
v_x_1605__boxed_1086_ = lean_unbox_usize(v_x_1082_);
lean_dec(v_x_1082_);
v_x_1606__boxed_1087_ = lean_unbox_usize(v_x_1083_);
lean_dec(v_x_1083_);
v_res_1088_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_1081_, v_x_1605__boxed_1086_, v_x_1606__boxed_1087_, v_x_1084_, v_x_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
uint64_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v___x_1092_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1090_);
v___x_1093_ = lean_uint64_to_usize(v___x_1092_);
v___x_1094_ = ((size_t)1ULL);
v___x_1095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_1089_, v___x_1093_, v___x_1094_, v_x_1090_, v_x_1091_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5_spec__10(lean_object* v_vs_1096_, lean_object* v_v_1097_, lean_object* v_i_1098_){
_start:
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = lean_array_get_size(v_vs_1096_);
v___x_1100_ = lean_nat_dec_lt(v_i_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_dec(v_i_1098_);
v___x_1101_ = lean_array_push(v_vs_1096_, v_v_1097_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_array_fget_borrowed(v_vs_1096_, v_i_1098_);
lean_inc(v___x_1102_);
lean_inc_ref(v_v_1097_);
v___x_1103_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(v_v_1097_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_i_1098_, v___x_1104_);
lean_dec(v_i_1098_);
v_i_1098_ = v___x_1105_;
goto _start;
}
else
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_array_fset(v_vs_1096_, v_i_1098_, v_v_1097_);
lean_dec(v_i_1098_);
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5(lean_object* v_vs_1108_, lean_object* v_v_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5_spec__10(v_vs_1108_, v_v_1109_, v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(lean_object* v_a_1112_, lean_object* v_b_1113_){
_start:
{
lean_object* v_fst_1114_; lean_object* v_fst_1115_; uint8_t v___x_1116_; 
v_fst_1114_ = lean_ctor_get(v_a_1112_, 0);
v_fst_1115_ = lean_ctor_get(v_b_1113_, 0);
v___x_1116_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1114_, v_fst_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1___boxed(lean_object* v_a_1117_, lean_object* v_b_1118_){
_start:
{
uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_res_1119_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_a_1117_, v_b_1118_);
lean_dec_ref(v_b_1118_);
lean_dec_ref(v_a_1117_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(lean_object* v_x_1121_, lean_object* v_keys_1122_, lean_object* v_v_1123_, lean_object* v_k_1124_, lean_object* v_x_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_c_1128_; lean_object* v___x_1129_; 
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_add(v_x_1121_, v___x_1126_);
v_c_1128_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1122_, v_v_1123_, v___x_1127_);
lean_dec(v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_k_1124_);
lean_ctor_set(v___x_1129_, 1, v_c_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v_x_1130_, lean_object* v_keys_1131_, lean_object* v_v_1132_, lean_object* v_k_1133_, lean_object* v_x_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_1130_, v_keys_1131_, v_v_1132_, v_k_1133_, v_x_1134_);
lean_dec_ref(v_keys_1131_);
lean_dec(v_x_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(lean_object* v_x_1140_, lean_object* v_keys_1141_, lean_object* v_v_1142_, lean_object* v_k_1143_, lean_object* v_as_1144_, lean_object* v_k_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_mid_1150_; lean_object* v_midVal_1151_; uint8_t v___x_1152_; 
v___x_1148_ = lean_nat_add(v_x_1146_, v_x_1147_);
v___x_1149_ = lean_unsigned_to_nat(1u);
v_mid_1150_ = lean_nat_shiftr(v___x_1148_, v___x_1149_);
lean_dec(v___x_1148_);
v_midVal_1151_ = lean_array_fget(v_as_1144_, v_mid_1150_);
v___x_1152_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_midVal_1151_, v_k_1145_);
if (v___x_1152_ == 0)
{
uint8_t v___x_1153_; 
lean_dec(v_x_1147_);
v___x_1153_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_k_1145_, v_midVal_1151_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
lean_dec(v_x_1146_);
v___x_1154_ = lean_array_get_size(v_as_1144_);
v___x_1155_ = lean_nat_dec_lt(v_mid_1150_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_dec(v_midVal_1151_);
lean_dec(v_mid_1150_);
lean_dec(v_k_1143_);
lean_dec_ref(v_v_1142_);
return v_as_1144_;
}
else
{
lean_object* v_snd_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1168_; 
v_snd_1156_ = lean_ctor_get(v_midVal_1151_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_midVal_1151_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v_midVal_1151_, 0);
lean_dec(v_unused_1169_);
v___x_1158_ = v_midVal_1151_;
v_isShared_1159_ = v_isSharedCheck_1168_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_snd_1156_);
lean_dec(v_midVal_1151_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1168_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v_xs_x27_1161_; lean_object* v___x_1162_; lean_object* v_c_1163_; lean_object* v___x_1165_; 
v___x_1160_ = lean_box(0);
v_xs_x27_1161_ = lean_array_fset(v_as_1144_, v_mid_1150_, v___x_1160_);
v___x_1162_ = lean_nat_add(v_x_1140_, v___x_1149_);
v_c_1163_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_1141_, v_v_1142_, v___x_1162_, v_snd_1156_);
lean_dec(v___x_1162_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 1, v_c_1163_);
lean_ctor_set(v___x_1158_, 0, v_k_1143_);
v___x_1165_ = v___x_1158_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_k_1143_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_c_1163_);
v___x_1165_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_array_fset(v_xs_x27_1161_, v_mid_1150_, v___x_1165_);
lean_dec(v_mid_1150_);
return v___x_1166_;
}
}
}
}
else
{
lean_dec(v_midVal_1151_);
v_x_1147_ = v_mid_1150_;
goto _start;
}
}
else
{
uint8_t v___x_1171_; 
lean_dec(v_midVal_1151_);
v___x_1171_ = lean_nat_dec_eq(v_mid_1150_, v_x_1146_);
if (v___x_1171_ == 0)
{
lean_dec(v_x_1146_);
v_x_1146_ = v_mid_1150_;
goto _start;
}
else
{
lean_object* v___x_1173_; lean_object* v_c_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_j_1177_; lean_object* v_as_1178_; lean_object* v___x_1179_; 
lean_dec(v_mid_1150_);
lean_dec(v_x_1147_);
v___x_1173_ = lean_nat_add(v_x_1140_, v___x_1149_);
v_c_1174_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1141_, v_v_1142_, v___x_1173_);
lean_dec(v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_k_1143_);
lean_ctor_set(v___x_1175_, 1, v_c_1174_);
v___x_1176_ = lean_nat_add(v_x_1146_, v___x_1149_);
lean_dec(v_x_1146_);
v_j_1177_ = lean_array_get_size(v_as_1144_);
v_as_1178_ = lean_array_push(v_as_1144_, v___x_1175_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1176_, v_as_1178_, v_j_1177_);
lean_dec(v___x_1176_);
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(lean_object* v_x_1180_, lean_object* v_keys_1181_, lean_object* v_v_1182_, lean_object* v_k_1183_, lean_object* v_as_1184_, lean_object* v_k_1185_){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = lean_array_get_size(v_as_1184_);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_nat_dec_eq(v___x_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_array_fget_borrowed(v_as_1184_, v___x_1187_);
v___x_1190_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_k_1185_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint8_t v___x_1191_; 
v___x_1191_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v___x_1189_, v_k_1185_);
if (v___x_1191_ == 0)
{
uint8_t v___x_1192_; 
v___x_1192_ = lean_nat_dec_lt(v___x_1187_, v___x_1186_);
if (v___x_1192_ == 0)
{
lean_dec(v_k_1183_);
lean_dec_ref(v_v_1182_);
return v_as_1184_;
}
else
{
lean_object* v___x_1193_; lean_object* v_xs_x27_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_inc(v___x_1189_);
v___x_1193_ = lean_box(0);
v_xs_x27_1194_ = lean_array_fset(v_as_1184_, v___x_1187_, v___x_1193_);
v___x_1195_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_1180_, v_keys_1181_, v_v_1182_, v_k_1183_, v___x_1189_);
v___x_1196_ = lean_array_fset(v_xs_x27_1194_, v___x_1187_, v___x_1195_);
return v___x_1196_;
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_nat_sub(v___x_1186_, v___x_1197_);
v___x_1199_ = lean_array_fget_borrowed(v_as_1184_, v___x_1198_);
v___x_1200_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v___x_1199_, v_k_1185_);
if (v___x_1200_ == 0)
{
uint8_t v___x_1201_; 
v___x_1201_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_k_1185_, v___x_1199_);
if (v___x_1201_ == 0)
{
uint8_t v___x_1202_; 
v___x_1202_ = lean_nat_dec_lt(v___x_1198_, v___x_1186_);
if (v___x_1202_ == 0)
{
lean_dec(v___x_1198_);
lean_dec(v_k_1183_);
lean_dec_ref(v_v_1182_);
return v_as_1184_;
}
else
{
lean_object* v___x_1203_; lean_object* v_xs_x27_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_inc(v___x_1199_);
v___x_1203_ = lean_box(0);
v_xs_x27_1204_ = lean_array_fset(v_as_1184_, v___x_1198_, v___x_1203_);
v___x_1205_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_1180_, v_keys_1181_, v_v_1182_, v_k_1183_, v___x_1199_);
v___x_1206_ = lean_array_fset(v_xs_x27_1204_, v___x_1198_, v___x_1205_);
lean_dec(v___x_1198_);
return v___x_1206_;
}
}
else
{
lean_object* v___x_1207_; 
v___x_1207_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1180_, v_keys_1181_, v_v_1182_, v_k_1183_, v_as_1184_, v_k_1185_, v___x_1187_, v___x_1198_);
return v___x_1207_;
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec(v___x_1198_);
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_1180_, v_keys_1181_, v_v_1182_, v_k_1183_, v___x_1208_);
v___x_1210_ = lean_array_push(v_as_1184_, v___x_1209_);
return v___x_1210_;
}
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v_as_1213_; lean_object* v___x_1214_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_1180_, v_keys_1181_, v_v_1182_, v_k_1183_, v___x_1211_);
v_as_1213_ = lean_array_push(v_as_1184_, v___x_1212_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1187_, v_as_1213_, v___x_1186_);
return v___x_1214_;
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_1180_, v_keys_1181_, v_v_1182_, v_k_1183_, v___x_1215_);
v___x_1217_ = lean_array_push(v_as_1184_, v___x_1216_);
return v___x_1217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(lean_object* v_keys_1218_, lean_object* v_v_1219_, lean_object* v_x_1220_, lean_object* v_x_1221_){
_start:
{
lean_object* v_vs_1222_; lean_object* v_children_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1240_; 
v_vs_1222_ = lean_ctor_get(v_x_1221_, 0);
v_children_1223_ = lean_ctor_get(v_x_1221_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_x_1221_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1225_ = v_x_1221_;
v_isShared_1226_ = v_isSharedCheck_1240_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_children_1223_);
lean_inc(v_vs_1222_);
lean_dec(v_x_1221_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1240_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = lean_array_get_size(v_keys_1218_);
v___x_1228_ = lean_nat_dec_lt(v_x_1220_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5(v_vs_1222_, v_v_1219_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1229_);
v___x_1231_ = v___x_1225_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_children_1223_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
else
{
lean_object* v_k_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_c_1236_; lean_object* v___x_1238_; 
v_k_1233_ = lean_array_fget_borrowed(v_keys_1218_, v_x_1220_);
v___x_1234_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1));
lean_inc_n(v_k_1233_, 2);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_k_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v_c_1236_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(v_x_1220_, v_keys_1218_, v_v_1219_, v_k_1233_, v_children_1223_, v___x_1235_);
lean_dec_ref(v___x_1235_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 1, v_c_1236_);
v___x_1238_ = v___x_1225_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_vs_1222_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_c_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(lean_object* v_x_1241_, lean_object* v_keys_1242_, lean_object* v_v_1243_, lean_object* v_k_1244_, lean_object* v_x_1245_){
_start:
{
lean_object* v_snd_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1256_; 
v_snd_1246_ = lean_ctor_get(v_x_1245_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1245_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_x_1245_, 0);
lean_dec(v_unused_1257_);
v___x_1248_ = v_x_1245_;
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_snd_1246_);
lean_dec(v_x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_c_1252_; lean_object* v___x_1254_; 
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v_x_1241_, v___x_1250_);
v_c_1252_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_1242_, v_v_1243_, v___x_1251_, v_snd_1246_);
lean_dec(v___x_1251_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v_c_1252_);
lean_ctor_set(v___x_1248_, 0, v_k_1244_);
v___x_1254_ = v___x_1248_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_k_1244_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_c_1252_);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2___boxed(lean_object* v_x_1258_, lean_object* v_keys_1259_, lean_object* v_v_1260_, lean_object* v_k_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_1258_, v_keys_1259_, v_v_1260_, v_k_1261_, v_x_1262_);
lean_dec_ref(v_keys_1259_);
lean_dec(v_x_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___boxed(lean_object* v_keys_1264_, lean_object* v_v_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_1264_, v_v_1265_, v_x_1266_, v_x_1267_);
lean_dec(v_x_1266_);
lean_dec_ref(v_keys_1264_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_x_1269_, lean_object* v_keys_1270_, lean_object* v_v_1271_, lean_object* v_k_1272_, lean_object* v_as_1273_, lean_object* v_k_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1269_, v_keys_1270_, v_v_1271_, v_k_1272_, v_as_1273_, v_k_1274_, v_x_1275_, v_x_1276_);
lean_dec_ref(v_k_1274_);
lean_dec_ref(v_keys_1270_);
lean_dec(v_x_1269_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___boxed(lean_object* v_x_1278_, lean_object* v_keys_1279_, lean_object* v_v_1280_, lean_object* v_k_1281_, lean_object* v_as_1282_, lean_object* v_k_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(v_x_1278_, v_keys_1279_, v_v_1280_, v_k_1281_, v_as_1282_, v_k_1283_);
lean_dec_ref(v_k_1283_);
lean_dec_ref(v_keys_1279_);
lean_dec(v_x_1278_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_1285_, lean_object* v_vals_1286_, lean_object* v_i_1287_, lean_object* v_k_1288_){
_start:
{
lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = lean_array_get_size(v_keys_1285_);
v___x_1290_ = lean_nat_dec_lt(v_i_1287_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
lean_dec(v_i_1287_);
v___x_1291_ = lean_box(0);
return v___x_1291_;
}
else
{
lean_object* v_k_x27_1292_; uint8_t v___x_1293_; 
v_k_x27_1292_ = lean_array_fget_borrowed(v_keys_1285_, v_i_1287_);
v___x_1293_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1288_, v_k_x27_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_add(v_i_1287_, v___x_1294_);
lean_dec(v_i_1287_);
v_i_1287_ = v___x_1295_;
goto _start;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_array_fget_borrowed(v_vals_1286_, v_i_1287_);
lean_dec(v_i_1287_);
lean_inc(v___x_1297_);
v___x_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_1299_, lean_object* v_vals_1300_, lean_object* v_i_1301_, lean_object* v_k_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1299_, v_vals_1300_, v_i_1301_, v_k_1302_);
lean_dec(v_k_1302_);
lean_dec_ref(v_vals_1300_);
lean_dec_ref(v_keys_1299_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1304_, size_t v_x_1305_, lean_object* v_x_1306_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 0)
{
lean_object* v_es_1307_; lean_object* v___x_1308_; size_t v___x_1309_; size_t v___x_1310_; size_t v___x_1311_; lean_object* v_j_1312_; lean_object* v___x_1313_; 
v_es_1307_ = lean_ctor_get(v_x_1304_, 0);
v___x_1308_ = lean_box(2);
v___x_1309_ = ((size_t)5ULL);
v___x_1310_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1311_ = lean_usize_land(v_x_1305_, v___x_1310_);
v_j_1312_ = lean_usize_to_nat(v___x_1311_);
v___x_1313_ = lean_array_get_borrowed(v___x_1308_, v_es_1307_, v_j_1312_);
lean_dec(v_j_1312_);
switch(lean_obj_tag(v___x_1313_))
{
case 0:
{
lean_object* v_key_1314_; lean_object* v_val_1315_; uint8_t v___x_1316_; 
v_key_1314_ = lean_ctor_get(v___x_1313_, 0);
v_val_1315_ = lean_ctor_get(v___x_1313_, 1);
v___x_1316_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1306_, v_key_1314_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_box(0);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; 
lean_inc(v_val_1315_);
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_val_1315_);
return v___x_1318_;
}
}
case 1:
{
lean_object* v_node_1319_; size_t v___x_1320_; 
v_node_1319_ = lean_ctor_get(v___x_1313_, 0);
v___x_1320_ = lean_usize_shift_right(v_x_1305_, v___x_1309_);
v_x_1304_ = v_node_1319_;
v_x_1305_ = v___x_1320_;
goto _start;
}
default: 
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_box(0);
return v___x_1322_;
}
}
}
else
{
lean_object* v_ks_1323_; lean_object* v_vs_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_ks_1323_ = lean_ctor_get(v_x_1304_, 0);
v_vs_1324_ = lean_ctor_get(v_x_1304_, 1);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_1323_, v_vs_1324_, v___x_1325_, v_x_1306_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
size_t v_x_2045__boxed_1330_; lean_object* v_res_1331_; 
v_x_2045__boxed_1330_ = lean_unbox_usize(v_x_1328_);
lean_dec(v_x_1328_);
v_res_1331_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_1327_, v_x_2045__boxed_1330_, v_x_1329_);
lean_dec(v_x_1329_);
lean_dec_ref(v_x_1327_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
uint64_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1333_);
v___x_1335_ = lean_uint64_to_usize(v___x_1334_);
v___x_1336_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_1332_, v___x_1335_, v_x_1333_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_1337_, lean_object* v_x_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_x_1337_, v_x_1338_);
lean_dec(v_x_1338_);
lean_dec_ref(v_x_1337_);
return v_res_1339_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3(lean_object* v_msg_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0);
v___x_1343_ = lean_panic_fn_borrowed(v___x_1342_, v_msg_1341_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1347_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2));
v___x_1348_ = lean_unsigned_to_nat(23u);
v___x_1349_ = lean_unsigned_to_nat(166u);
v___x_1350_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1));
v___x_1351_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0));
v___x_1352_ = l_mkPanicMessageWithDecl(v___x_1351_, v___x_1350_, v___x_1349_, v___x_1348_, v___x_1347_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(lean_object* v_d_1353_, lean_object* v_keys_1354_, lean_object* v_v_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = lean_array_get_size(v_keys_1354_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_nat_dec_eq(v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v_k_1360_; lean_object* v___x_1361_; 
v___x_1359_ = lean_box(0);
v_k_1360_ = lean_array_get_borrowed(v___x_1359_, v_keys_1354_, v___x_1357_);
v___x_1361_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_d_1353_, v_k_1360_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v___x_1362_; lean_object* v_c_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_unsigned_to_nat(1u);
v_c_1363_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1354_, v_v_1355_, v___x_1362_);
lean_inc(v_k_1360_);
v___x_1364_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_d_1353_, v_k_1360_, v_c_1363_);
return v___x_1364_;
}
else
{
lean_object* v_val_1365_; lean_object* v___x_1366_; lean_object* v_c_1367_; lean_object* v___x_1368_; 
v_val_1365_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_val_1365_);
lean_dec_ref(v___x_1361_);
v___x_1366_ = lean_unsigned_to_nat(1u);
v_c_1367_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_1354_, v_v_1355_, v___x_1366_, v_val_1365_);
lean_inc(v_k_1360_);
v___x_1368_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_d_1353_, v_k_1360_, v_c_1367_);
return v___x_1368_;
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec_ref(v_v_1355_);
lean_dec_ref(v_d_1353_);
v___x_1369_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3);
v___x_1370_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3(v___x_1369_);
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___boxed(lean_object* v_d_1371_, lean_object* v_keys_1372_, lean_object* v_v_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(v_d_1371_, v_keys_1372_, v_v_1373_);
lean_dec_ref(v_keys_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(lean_object* v_d_1375_, lean_object* v_e_1376_){
_start:
{
lean_object* v_specs_1377_; lean_object* v_erased_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1387_; 
v_specs_1377_ = lean_ctor_get(v_d_1375_, 0);
v_erased_1378_ = lean_ctor_get(v_d_1375_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_d_1375_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1380_ = v_d_1375_;
v_isShared_1381_ = v_isSharedCheck_1387_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_erased_1378_);
lean_inc(v_specs_1377_);
lean_dec(v_d_1375_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1387_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_keys_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v_keys_1382_ = lean_ctor_get(v_e_1376_, 0);
lean_inc_ref(v_keys_1382_);
v___x_1383_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(v_specs_1377_, v_keys_1382_, v_e_1376_);
lean_dec_ref(v_keys_1382_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1383_);
v___x_1385_ = v___x_1380_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_erased_1378_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(lean_object* v_00_u03b2_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_x_1389_, v_x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(v_00_u03b2_1392_, v_x_1393_, v_x_1394_);
lean_dec(v_x_1394_);
lean_dec_ref(v_x_1393_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1(lean_object* v_00_u03b2_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_x_1397_, v_x_1398_, v_x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1401_, lean_object* v_x_1402_, size_t v_x_1403_, lean_object* v_x_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_1402_, v_x_1403_, v_x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
size_t v_x_2196__boxed_1410_; lean_object* v_res_1411_; 
v_x_2196__boxed_1410_ = lean_unbox_usize(v_x_1408_);
lean_dec(v_x_1408_);
v_res_1411_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(v_00_u03b2_1406_, v_x_1407_, v_x_2196__boxed_1410_, v_x_1409_);
lean_dec(v_x_1409_);
lean_dec_ref(v_x_1407_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1412_, lean_object* v_x_1413_, size_t v_x_1414_, size_t v_x_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_1413_, v_x_1414_, v_x_1415_, v_x_1416_, v_x_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
size_t v_x_2207__boxed_1425_; size_t v_x_2208__boxed_1426_; lean_object* v_res_1427_; 
v_x_2207__boxed_1425_ = lean_unbox_usize(v_x_1421_);
lean_dec(v_x_1421_);
v_x_2208__boxed_1426_ = lean_unbox_usize(v_x_1422_);
lean_dec(v_x_1422_);
v_res_1427_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3(v_00_u03b2_1419_, v_x_1420_, v_x_2207__boxed_1425_, v_x_2208__boxed_1426_, v_x_1423_, v_x_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1428_, lean_object* v_keys_1429_, lean_object* v_vals_1430_, lean_object* v_heq_1431_, lean_object* v_i_1432_, lean_object* v_k_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1429_, v_vals_1430_, v_i_1432_, v_k_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1435_, lean_object* v_keys_1436_, lean_object* v_vals_1437_, lean_object* v_heq_1438_, lean_object* v_i_1439_, lean_object* v_k_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1435_, v_keys_1436_, v_vals_1437_, v_heq_1438_, v_i_1439_, v_k_1440_);
lean_dec(v_k_1440_);
lean_dec_ref(v_vals_1437_);
lean_dec_ref(v_keys_1436_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1442_, lean_object* v_n_1443_, lean_object* v_k_1444_, lean_object* v_v_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(v_n_1443_, v_k_1444_, v_v_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_1447_, size_t v_depth_1448_, lean_object* v_keys_1449_, lean_object* v_vals_1450_, lean_object* v_heq_1451_, lean_object* v_i_1452_, lean_object* v_entries_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_1448_, v_keys_1449_, v_vals_1450_, v_i_1452_, v_entries_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1455_, lean_object* v_depth_1456_, lean_object* v_keys_1457_, lean_object* v_vals_1458_, lean_object* v_heq_1459_, lean_object* v_i_1460_, lean_object* v_entries_1461_){
_start:
{
size_t v_depth_boxed_1462_; lean_object* v_res_1463_; 
v_depth_boxed_1462_ = lean_unbox_usize(v_depth_1456_);
lean_dec(v_depth_1456_);
v_res_1463_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_1455_, v_depth_boxed_1462_, v_keys_1457_, v_vals_1458_, v_heq_1459_, v_i_1460_, v_entries_1461_);
lean_dec_ref(v_vals_1458_);
lean_dec_ref(v_keys_1457_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12(lean_object* v_x_1464_, lean_object* v_keys_1465_, lean_object* v_v_1466_, lean_object* v_k_1467_, lean_object* v_as_1468_, lean_object* v_k_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1464_, v_keys_1465_, v_v_1466_, v_k_1467_, v_as_1468_, v_k_1469_, v_x_1470_, v_x_1471_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_x_1475_, lean_object* v_keys_1476_, lean_object* v_v_1477_, lean_object* v_k_1478_, lean_object* v_as_1479_, lean_object* v_k_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12(v_x_1475_, v_keys_1476_, v_v_1477_, v_k_1478_, v_as_1479_, v_k_1480_, v_x_1481_, v_x_1482_, v_x_1483_, v_x_1484_);
lean_dec_ref(v_k_1480_);
lean_dec_ref(v_keys_1476_);
lean_dec(v_x_1475_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_1487_, v_x_1488_, v_x_1489_, v_x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1492_, lean_object* v_i_1493_, lean_object* v_k_1494_){
_start:
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = lean_array_get_size(v_keys_1492_);
v___x_1496_ = lean_nat_dec_lt(v_i_1493_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_dec_ref(v_k_1494_);
lean_dec(v_i_1493_);
return v___x_1496_;
}
else
{
lean_object* v_k_x27_1497_; uint8_t v___x_1498_; 
v_k_x27_1497_ = lean_array_fget_borrowed(v_keys_1492_, v_i_1493_);
lean_inc(v_k_x27_1497_);
lean_inc_ref(v_k_1494_);
v___x_1498_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_k_1494_, v_k_x27_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_i_1493_, v___x_1499_);
lean_dec(v_i_1493_);
v_i_1493_ = v___x_1500_;
goto _start;
}
else
{
lean_dec_ref(v_k_1494_);
lean_dec(v_i_1493_);
return v___x_1498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1502_, lean_object* v_i_1503_, lean_object* v_k_1504_){
_start:
{
uint8_t v_res_1505_; lean_object* v_r_1506_; 
v_res_1505_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_1502_, v_i_1503_, v_k_1504_);
lean_dec_ref(v_keys_1502_);
v_r_1506_ = lean_box(v_res_1505_);
return v_r_1506_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(lean_object* v_x_1507_, size_t v_x_1508_, lean_object* v_x_1509_){
_start:
{
if (lean_obj_tag(v_x_1507_) == 0)
{
lean_object* v_es_1510_; lean_object* v___x_1511_; size_t v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; lean_object* v_j_1515_; lean_object* v___x_1516_; 
v_es_1510_ = lean_ctor_get(v_x_1507_, 0);
lean_inc_ref(v_es_1510_);
lean_dec_ref(v_x_1507_);
v___x_1511_ = lean_box(2);
v___x_1512_ = ((size_t)5ULL);
v___x_1513_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1514_ = lean_usize_land(v_x_1508_, v___x_1513_);
v_j_1515_ = lean_usize_to_nat(v___x_1514_);
v___x_1516_ = lean_array_get(v___x_1511_, v_es_1510_, v_j_1515_);
lean_dec(v_j_1515_);
lean_dec_ref(v_es_1510_);
switch(lean_obj_tag(v___x_1516_))
{
case 0:
{
lean_object* v_key_1517_; uint8_t v___x_1518_; 
v_key_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_key_1517_);
lean_dec_ref(v___x_1516_);
v___x_1518_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1509_, v_key_1517_);
return v___x_1518_;
}
case 1:
{
lean_object* v_node_1519_; size_t v___x_1520_; 
v_node_1519_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_node_1519_);
lean_dec_ref(v___x_1516_);
v___x_1520_ = lean_usize_shift_right(v_x_1508_, v___x_1512_);
v_x_1507_ = v_node_1519_;
v_x_1508_ = v___x_1520_;
goto _start;
}
default: 
{
uint8_t v___x_1522_; 
lean_dec_ref(v_x_1509_);
v___x_1522_ = 0;
return v___x_1522_;
}
}
}
else
{
lean_object* v_ks_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v_ks_1523_ = lean_ctor_get(v_x_1507_, 0);
lean_inc_ref(v_ks_1523_);
lean_dec_ref(v_x_1507_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_ks_1523_, v___x_1524_, v_x_1509_);
lean_dec_ref(v_ks_1523_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg___boxed(lean_object* v_x_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_){
_start:
{
size_t v_x_146__boxed_1529_; uint8_t v_res_1530_; lean_object* v_r_1531_; 
v_x_146__boxed_1529_ = lean_unbox_usize(v_x_1527_);
lean_dec(v_x_1527_);
v_res_1530_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_1526_, v_x_146__boxed_1529_, v_x_1528_);
v_r_1531_ = lean_box(v_res_1530_);
return v_r_1531_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
uint64_t v___y_1535_; lean_object* v___y_1539_; lean_object* v_declName_1542_; 
v_declName_1542_ = lean_ctor_get(v_x_1533_, 0);
lean_inc(v_declName_1542_);
v___y_1539_ = v_declName_1542_;
goto v___jp_1538_;
v___jp_1534_:
{
size_t v___x_1536_; uint8_t v___x_1537_; 
v___x_1536_ = lean_uint64_to_usize(v___y_1535_);
v___x_1537_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_1532_, v___x_1536_, v_x_1533_);
return v___x_1537_;
}
v___jp_1538_:
{
if (lean_obj_tag(v___y_1539_) == 0)
{
uint64_t v___x_1540_; 
v___x_1540_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_1535_ = v___x_1540_;
goto v___jp_1534_;
}
else
{
uint64_t v_hash_1541_; 
v_hash_1541_ = lean_ctor_get_uint64(v___y_1539_, sizeof(void*)*2);
lean_dec(v___y_1539_);
v___y_1535_ = v_hash_1541_;
goto v___jp_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg___boxed(lean_object* v_x_1543_, lean_object* v_x_1544_){
_start:
{
uint8_t v_res_1545_; lean_object* v_r_1546_; 
v_res_1545_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_1543_, v_x_1544_);
v_r_1546_ = lean_box(v_res_1545_);
return v_r_1546_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(lean_object* v_d_1547_, lean_object* v_thmId_1548_){
_start:
{
lean_object* v_erased_1549_; uint8_t v___x_1550_; 
v_erased_1549_ = lean_ctor_get(v_d_1547_, 1);
lean_inc_ref(v_erased_1549_);
lean_dec_ref(v_d_1547_);
v___x_1550_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_erased_1549_, v_thmId_1548_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased___boxed(lean_object* v_d_1551_, lean_object* v_thmId_1552_){
_start:
{
uint8_t v_res_1553_; lean_object* v_r_1554_; 
v_res_1553_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_d_1551_, v_thmId_1552_);
v_r_1554_ = lean_box(v_res_1553_);
return v_r_1554_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(lean_object* v_00_u03b2_1555_, lean_object* v_x_1556_, lean_object* v_x_1557_){
_start:
{
uint8_t v___x_1558_; 
v___x_1558_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_1556_, v_x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___boxed(lean_object* v_00_u03b2_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_){
_start:
{
uint8_t v_res_1562_; lean_object* v_r_1563_; 
v_res_1562_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(v_00_u03b2_1559_, v_x_1560_, v_x_1561_);
v_r_1563_ = lean_box(v_res_1562_);
return v_r_1563_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(lean_object* v_00_u03b2_1564_, lean_object* v_x_1565_, size_t v_x_1566_, lean_object* v_x_1567_){
_start:
{
uint8_t v___x_1568_; 
v___x_1568_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_1565_, v_x_1566_, v_x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1569_, lean_object* v_x_1570_, lean_object* v_x_1571_, lean_object* v_x_1572_){
_start:
{
size_t v_x_228__boxed_1573_; uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_x_228__boxed_1573_ = lean_unbox_usize(v_x_1571_);
lean_dec(v_x_1571_);
v_res_1574_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(v_00_u03b2_1569_, v_x_1570_, v_x_228__boxed_1573_, v_x_1572_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1576_, lean_object* v_keys_1577_, lean_object* v_vals_1578_, lean_object* v_heq_1579_, lean_object* v_i_1580_, lean_object* v_k_1581_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_1577_, v_i_1580_, v_k_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1583_, lean_object* v_keys_1584_, lean_object* v_vals_1585_, lean_object* v_heq_1586_, lean_object* v_i_1587_, lean_object* v_k_1588_){
_start:
{
uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_res_1589_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(v_00_u03b2_1583_, v_keys_1584_, v_vals_1585_, v_heq_1586_, v_i_1587_, v_k_1588_);
lean_dec_ref(v_vals_1585_);
lean_dec_ref(v_keys_1584_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v_ks_1595_; lean_object* v_vs_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1620_; 
v_ks_1595_ = lean_ctor_get(v_x_1591_, 0);
v_vs_1596_ = lean_ctor_get(v_x_1591_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_x_1591_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1598_ = v_x_1591_;
v_isShared_1599_ = v_isSharedCheck_1620_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_vs_1596_);
lean_inc(v_ks_1595_);
lean_dec(v_x_1591_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1620_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = lean_array_get_size(v_ks_1595_);
v___x_1601_ = lean_nat_dec_lt(v_x_1592_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_dec(v_x_1592_);
v___x_1602_ = lean_array_push(v_ks_1595_, v_x_1593_);
v___x_1603_ = lean_array_push(v_vs_1596_, v_x_1594_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v___x_1603_);
lean_ctor_set(v___x_1598_, 0, v___x_1602_);
v___x_1605_ = v___x_1598_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
else
{
lean_object* v_k_x27_1607_; uint8_t v___x_1608_; 
v_k_x27_1607_ = lean_array_fget_borrowed(v_ks_1595_, v_x_1592_);
lean_inc(v_k_x27_1607_);
lean_inc_ref(v_x_1593_);
v___x_1608_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1593_, v_k_x27_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1610_; 
if (v_isShared_1599_ == 0)
{
v___x_1610_ = v___x_1598_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_ks_1595_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_vs_1596_);
v___x_1610_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_unsigned_to_nat(1u);
v___x_1612_ = lean_nat_add(v_x_1592_, v___x_1611_);
lean_dec(v_x_1592_);
v_x_1591_ = v___x_1610_;
v_x_1592_ = v___x_1612_;
goto _start;
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1615_ = lean_array_fset(v_ks_1595_, v_x_1592_, v_x_1593_);
v___x_1616_ = lean_array_fset(v_vs_1596_, v_x_1592_, v_x_1594_);
lean_dec(v_x_1592_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v___x_1616_);
lean_ctor_set(v___x_1598_, 0, v___x_1615_);
v___x_1618_ = v___x_1598_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v___x_1616_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1621_, lean_object* v_k_1622_, lean_object* v_v_1623_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_unsigned_to_nat(0u);
v___x_1625_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1621_, v___x_1624_, v_k_1622_, v_v_1623_);
return v___x_1625_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(lean_object* v_x_1627_, size_t v_x_1628_, size_t v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
if (lean_obj_tag(v_x_1627_) == 0)
{
lean_object* v_es_1632_; size_t v___x_1633_; size_t v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; lean_object* v_j_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v_es_1632_ = lean_ctor_get(v_x_1627_, 0);
v___x_1633_ = ((size_t)5ULL);
v___x_1634_ = ((size_t)1ULL);
v___x_1635_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1636_ = lean_usize_land(v_x_1628_, v___x_1635_);
v_j_1637_ = lean_usize_to_nat(v___x_1636_);
v___x_1638_ = lean_array_get_size(v_es_1632_);
v___x_1639_ = lean_nat_dec_lt(v_j_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_dec(v_j_1637_);
lean_dec(v_x_1631_);
lean_dec_ref(v_x_1630_);
return v_x_1627_;
}
else
{
lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1676_; 
lean_inc_ref(v_es_1632_);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_x_1627_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v_x_1627_, 0);
lean_dec(v_unused_1677_);
v___x_1641_ = v_x_1627_;
v_isShared_1642_ = v_isSharedCheck_1676_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v_x_1627_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1676_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v_v_1643_; lean_object* v___x_1644_; lean_object* v_xs_x27_1645_; lean_object* v___y_1647_; 
v_v_1643_ = lean_array_fget(v_es_1632_, v_j_1637_);
v___x_1644_ = lean_box(0);
v_xs_x27_1645_ = lean_array_fset(v_es_1632_, v_j_1637_, v___x_1644_);
switch(lean_obj_tag(v_v_1643_))
{
case 0:
{
lean_object* v_key_1652_; lean_object* v_val_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1663_; 
v_key_1652_ = lean_ctor_get(v_v_1643_, 0);
v_val_1653_ = lean_ctor_get(v_v_1643_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_v_1643_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1655_ = v_v_1643_;
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_val_1653_);
lean_inc(v_key_1652_);
lean_dec(v_v_1643_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
uint8_t v___x_1657_; 
lean_inc(v_key_1652_);
lean_inc_ref(v_x_1630_);
v___x_1657_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1630_, v_key_1652_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_del_object(v___x_1655_);
v___x_1658_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1652_, v_val_1653_, v_x_1630_, v_x_1631_);
v___x_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
v___y_1647_ = v___x_1659_;
goto v___jp_1646_;
}
else
{
lean_object* v___x_1661_; 
lean_dec(v_val_1653_);
lean_dec(v_key_1652_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v_x_1631_);
lean_ctor_set(v___x_1655_, 0, v_x_1630_);
v___x_1661_ = v___x_1655_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_x_1630_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_x_1631_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
v___y_1647_ = v___x_1661_;
goto v___jp_1646_;
}
}
}
}
case 1:
{
lean_object* v_node_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1674_; 
v_node_1664_ = lean_ctor_get(v_v_1643_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_v_1643_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1666_ = v_v_1643_;
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_node_1664_);
lean_dec(v_v_1643_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
size_t v___x_1668_; size_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1668_ = lean_usize_shift_right(v_x_1628_, v___x_1633_);
v___x_1669_ = lean_usize_add(v_x_1629_, v___x_1634_);
v___x_1670_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_node_1664_, v___x_1668_, v___x_1669_, v_x_1630_, v_x_1631_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1670_);
v___x_1672_ = v___x_1666_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
v___y_1647_ = v___x_1672_;
goto v___jp_1646_;
}
}
}
default: 
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_x_1630_);
lean_ctor_set(v___x_1675_, 1, v_x_1631_);
v___y_1647_ = v___x_1675_;
goto v___jp_1646_;
}
}
v___jp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = lean_array_fset(v_xs_x27_1645_, v_j_1637_, v___y_1647_);
lean_dec(v_j_1637_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1648_);
v___x_1650_ = v___x_1641_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
else
{
lean_object* v_ks_1678_; lean_object* v_vs_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1699_; 
v_ks_1678_ = lean_ctor_get(v_x_1627_, 0);
v_vs_1679_ = lean_ctor_get(v_x_1627_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_x_1627_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1681_ = v_x_1627_;
v_isShared_1682_ = v_isSharedCheck_1699_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_vs_1679_);
lean_inc(v_ks_1678_);
lean_dec(v_x_1627_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1699_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_ks_1678_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_vs_1679_);
v___x_1684_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v_newNode_1685_; uint8_t v___y_1687_; size_t v___x_1693_; uint8_t v___x_1694_; 
v_newNode_1685_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v___x_1684_, v_x_1630_, v_x_1631_);
v___x_1693_ = ((size_t)7ULL);
v___x_1694_ = lean_usize_dec_le(v___x_1693_, v_x_1629_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1695_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1685_);
v___x_1696_ = lean_unsigned_to_nat(4u);
v___x_1697_ = lean_nat_dec_lt(v___x_1695_, v___x_1696_);
lean_dec(v___x_1695_);
v___y_1687_ = v___x_1697_;
goto v___jp_1686_;
}
else
{
v___y_1687_ = v___x_1694_;
goto v___jp_1686_;
}
v___jp_1686_:
{
if (v___y_1687_ == 0)
{
lean_object* v_ks_1688_; lean_object* v_vs_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_ks_1688_ = lean_ctor_get(v_newNode_1685_, 0);
lean_inc_ref(v_ks_1688_);
v_vs_1689_ = lean_ctor_get(v_newNode_1685_, 1);
lean_inc_ref(v_vs_1689_);
lean_dec_ref(v_newNode_1685_);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0);
v___x_1692_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_x_1629_, v_ks_1688_, v_vs_1689_, v___x_1690_, v___x_1691_);
lean_dec_ref(v_vs_1689_);
lean_dec_ref(v_ks_1688_);
return v___x_1692_;
}
else
{
return v_newNode_1685_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(size_t v_depth_1700_, lean_object* v_keys_1701_, lean_object* v_vals_1702_, lean_object* v_i_1703_, lean_object* v_entries_1704_){
_start:
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = lean_array_get_size(v_keys_1701_);
v___x_1706_ = lean_nat_dec_lt(v_i_1703_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_dec(v_i_1703_);
return v_entries_1704_;
}
else
{
lean_object* v_k_1707_; lean_object* v_v_1708_; uint64_t v___y_1710_; lean_object* v___y_1722_; lean_object* v_declName_1725_; 
v_k_1707_ = lean_array_fget_borrowed(v_keys_1701_, v_i_1703_);
v_v_1708_ = lean_array_fget_borrowed(v_vals_1702_, v_i_1703_);
v_declName_1725_ = lean_ctor_get(v_k_1707_, 0);
lean_inc(v_declName_1725_);
v___y_1722_ = v_declName_1725_;
goto v___jp_1721_;
v___jp_1709_:
{
size_t v_h_1711_; size_t v___x_1712_; lean_object* v___x_1713_; size_t v___x_1714_; size_t v___x_1715_; size_t v___x_1716_; size_t v_h_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_h_1711_ = lean_uint64_to_usize(v___y_1710_);
v___x_1712_ = ((size_t)5ULL);
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = ((size_t)1ULL);
v___x_1715_ = lean_usize_sub(v_depth_1700_, v___x_1714_);
v___x_1716_ = lean_usize_mul(v___x_1712_, v___x_1715_);
v_h_1717_ = lean_usize_shift_right(v_h_1711_, v___x_1716_);
v___x_1718_ = lean_nat_add(v_i_1703_, v___x_1713_);
lean_dec(v_i_1703_);
lean_inc(v_v_1708_);
lean_inc(v_k_1707_);
v___x_1719_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_entries_1704_, v_h_1717_, v_depth_1700_, v_k_1707_, v_v_1708_);
v_i_1703_ = v___x_1718_;
v_entries_1704_ = v___x_1719_;
goto _start;
}
v___jp_1721_:
{
if (lean_obj_tag(v___y_1722_) == 0)
{
uint64_t v___x_1723_; 
v___x_1723_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_1710_ = v___x_1723_;
goto v___jp_1709_;
}
else
{
uint64_t v_hash_1724_; 
v_hash_1724_ = lean_ctor_get_uint64(v___y_1722_, sizeof(void*)*2);
lean_dec(v___y_1722_);
v___y_1710_ = v_hash_1724_;
goto v___jp_1709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1726_, lean_object* v_keys_1727_, lean_object* v_vals_1728_, lean_object* v_i_1729_, lean_object* v_entries_1730_){
_start:
{
size_t v_depth_boxed_1731_; lean_object* v_res_1732_; 
v_depth_boxed_1731_ = lean_unbox_usize(v_depth_1726_);
lean_dec(v_depth_1726_);
v_res_1732_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1731_, v_keys_1727_, v_vals_1728_, v_i_1729_, v_entries_1730_);
lean_dec_ref(v_vals_1728_);
lean_dec_ref(v_keys_1727_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v_x_1736_, lean_object* v_x_1737_){
_start:
{
size_t v_x_400__boxed_1738_; size_t v_x_401__boxed_1739_; lean_object* v_res_1740_; 
v_x_400__boxed_1738_ = lean_unbox_usize(v_x_1734_);
lean_dec(v_x_1734_);
v_x_401__boxed_1739_ = lean_unbox_usize(v_x_1735_);
lean_dec(v_x_1735_);
v_res_1740_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_1733_, v_x_400__boxed_1738_, v_x_401__boxed_1739_, v_x_1736_, v_x_1737_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(lean_object* v_x_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_){
_start:
{
uint64_t v___y_1745_; lean_object* v___y_1750_; lean_object* v_declName_1753_; 
v_declName_1753_ = lean_ctor_get(v_x_1742_, 0);
lean_inc(v_declName_1753_);
v___y_1750_ = v_declName_1753_;
goto v___jp_1749_;
v___jp_1744_:
{
size_t v___x_1746_; size_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = lean_uint64_to_usize(v___y_1745_);
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_1741_, v___x_1746_, v___x_1747_, v_x_1742_, v_x_1743_);
return v___x_1748_;
}
v___jp_1749_:
{
if (lean_obj_tag(v___y_1750_) == 0)
{
uint64_t v___x_1751_; 
v___x_1751_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_1745_ = v___x_1751_;
goto v___jp_1744_;
}
else
{
uint64_t v_hash_1752_; 
v_hash_1752_ = lean_ctor_get_uint64(v___y_1750_, sizeof(void*)*2);
lean_dec(v___y_1750_);
v___y_1745_ = v_hash_1752_;
goto v___jp_1744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(lean_object* v_d_1754_, lean_object* v_thmId_1755_){
_start:
{
lean_object* v_specs_1756_; lean_object* v_erased_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1766_; 
v_specs_1756_ = lean_ctor_get(v_d_1754_, 0);
v_erased_1757_ = lean_ctor_get(v_d_1754_, 1);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_d_1754_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1759_ = v_d_1754_;
v_isShared_1760_ = v_isSharedCheck_1766_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_erased_1757_);
lean_inc(v_specs_1756_);
lean_dec(v_d_1754_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1766_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1761_ = lean_box(0);
v___x_1762_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_erased_1757_, v_thmId_1755_, v___x_1761_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 1, v___x_1762_);
v___x_1764_ = v___x_1759_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_specs_1756_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0(lean_object* v_00_u03b2_1767_, lean_object* v_x_1768_, lean_object* v_x_1769_, lean_object* v_x_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_x_1768_, v_x_1769_, v_x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(lean_object* v_00_u03b2_1772_, lean_object* v_x_1773_, size_t v_x_1774_, size_t v_x_1775_, lean_object* v_x_1776_, lean_object* v_x_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_1773_, v_x_1774_, v_x_1775_, v_x_1776_, v_x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1779_, lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_){
_start:
{
size_t v_x_618__boxed_1785_; size_t v_x_619__boxed_1786_; lean_object* v_res_1787_; 
v_x_618__boxed_1785_ = lean_unbox_usize(v_x_1781_);
lean_dec(v_x_1781_);
v_x_619__boxed_1786_ = lean_unbox_usize(v_x_1782_);
lean_dec(v_x_1782_);
v_res_1787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(v_00_u03b2_1779_, v_x_1780_, v_x_618__boxed_1785_, v_x_619__boxed_1786_, v_x_1783_, v_x_1784_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1788_, lean_object* v_n_1789_, lean_object* v_k_1790_, lean_object* v_v_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v_n_1789_, v_k_1790_, v_v_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1793_, size_t v_depth_1794_, lean_object* v_keys_1795_, lean_object* v_vals_1796_, lean_object* v_heq_1797_, lean_object* v_i_1798_, lean_object* v_entries_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_1794_, v_keys_1795_, v_vals_1796_, v_i_1798_, v_entries_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1801_, lean_object* v_depth_1802_, lean_object* v_keys_1803_, lean_object* v_vals_1804_, lean_object* v_heq_1805_, lean_object* v_i_1806_, lean_object* v_entries_1807_){
_start:
{
size_t v_depth_boxed_1808_; lean_object* v_res_1809_; 
v_depth_boxed_1808_ = lean_unbox_usize(v_depth_1802_);
lean_dec(v_depth_1802_);
v_res_1809_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(v_00_u03b2_1801_, v_depth_boxed_1808_, v_keys_1803_, v_vals_1804_, v_heq_1805_, v_i_1806_, v_entries_1807_);
lean_dec_ref(v_vals_1804_);
lean_dec_ref(v_keys_1803_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_, lean_object* v_x_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1811_, v_x_1812_, v_x_1813_, v_x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(lean_object* v_a_1816_, lean_object* v_as_1817_, size_t v_i_1818_, size_t v_stop_1819_){
_start:
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_usize_dec_eq(v_i_1818_, v_stop_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = lean_array_uget_borrowed(v_as_1817_, v_i_1818_);
v___x_1822_ = lean_expr_eqv(v_a_1816_, v___x_1821_);
if (v___x_1822_ == 0)
{
size_t v___x_1823_; size_t v___x_1824_; 
v___x_1823_ = ((size_t)1ULL);
v___x_1824_ = lean_usize_add(v_i_1818_, v___x_1823_);
v_i_1818_ = v___x_1824_;
goto _start;
}
else
{
return v___x_1822_;
}
}
else
{
uint8_t v___x_1826_; 
v___x_1826_ = 0;
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0___boxed(lean_object* v_a_1827_, lean_object* v_as_1828_, lean_object* v_i_1829_, lean_object* v_stop_1830_){
_start:
{
size_t v_i_boxed_1831_; size_t v_stop_boxed_1832_; uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_i_boxed_1831_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_stop_boxed_1832_ = lean_unbox_usize(v_stop_1830_);
lean_dec(v_stop_1830_);
v_res_1833_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(v_a_1827_, v_as_1828_, v_i_boxed_1831_, v_stop_boxed_1832_);
lean_dec_ref(v_as_1828_);
lean_dec_ref(v_a_1827_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(lean_object* v_as_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_array_get_size(v_as_1835_);
v___x_1839_ = lean_nat_dec_lt(v___x_1837_, v___x_1838_);
if (v___x_1839_ == 0)
{
return v___x_1839_;
}
else
{
if (v___x_1839_ == 0)
{
return v___x_1839_;
}
else
{
size_t v___x_1840_; size_t v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = ((size_t)0ULL);
v___x_1841_ = lean_usize_of_nat(v___x_1838_);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(v_a_1836_, v_as_1835_, v___x_1840_, v___x_1841_);
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0___boxed(lean_object* v_as_1843_, lean_object* v_a_1844_){
_start:
{
uint8_t v_res_1845_; lean_object* v_r_1846_; 
v_res_1845_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_as_1843_, v_a_1844_);
lean_dec_ref(v_a_1844_);
lean_dec_ref(v_as_1843_);
v_r_1846_ = lean_box(v_res_1845_);
return v_r_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(lean_object* v_xs_1850_, lean_object* v_e_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_ty_1858_; lean_object* v_b_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___x_1876_; 
v___x_1876_ = l_Lean_Expr_hasExprMVar(v_e_1851_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
else
{
switch(lean_obj_tag(v_e_1851_))
{
case 5:
{
lean_object* v_fn_1879_; lean_object* v_arg_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v_fn_1879_ = lean_ctor_get(v_e_1851_, 0);
v_arg_1880_ = lean_ctor_get(v_e_1851_, 1);
v___x_1881_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1));
v___x_1882_ = lean_unsigned_to_nat(3u);
v___x_1883_ = l_Lean_Expr_isAppOfArity(v_e_1851_, v___x_1881_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1850_, v_fn_1879_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1886_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1850_, v_arg_1880_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1895_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = lean_nat_add(v_a_1885_, v_a_1887_);
lean_dec(v_a_1887_);
lean_dec(v_a_1885_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_dec(v_a_1885_);
return v___x_1886_;
}
}
else
{
return v___x_1884_;
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_l_1912_; lean_object* v_r_1913_; uint8_t v___y_1915_; uint8_t v___y_1923_; uint8_t v___x_1927_; 
v___x_1896_ = l_Lean_Expr_appFn_x21(v_e_1851_);
v___x_1897_ = l_Lean_Expr_appArg_x21(v___x_1896_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = l_Lean_Expr_appArg_x21(v_e_1851_);
v_l_1912_ = l_Lean_Expr_getAppFn_x27(v___x_1897_);
v_r_1913_ = l_Lean_Expr_getAppFn_x27(v___x_1898_);
v___x_1927_ = l_Lean_Expr_isMVar(v_l_1912_);
if (v___x_1927_ == 0)
{
v___y_1923_ = v___x_1927_;
goto v___jp_1922_;
}
else
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Expr_hasLooseBVars(v___x_1898_);
v___y_1923_ = v___x_1928_;
goto v___jp_1922_;
}
v___jp_1899_:
{
lean_object* v___x_1900_; 
v___x_1900_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1850_, v___x_1897_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
lean_dec_ref(v___x_1897_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1902_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref(v___x_1900_);
v___x_1902_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1850_, v___x_1898_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
lean_dec_ref(v___x_1898_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1911_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_nat_add(v_a_1901_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec(v_a_1901_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1907_);
v___x_1909_ = v___x_1905_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
lean_dec(v_a_1901_);
return v___x_1902_;
}
}
else
{
lean_dec_ref(v___x_1898_);
return v___x_1900_;
}
}
v___jp_1914_:
{
if (v___y_1915_ == 0)
{
lean_dec_ref(v_r_1913_);
goto v___jp_1899_;
}
else
{
uint8_t v___x_1916_; 
v___x_1916_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_xs_1850_, v_r_1913_);
lean_dec_ref(v_r_1913_);
if (v___x_1916_ == 0)
{
goto v___jp_1899_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec_ref(v___x_1898_);
lean_dec_ref(v___x_1897_);
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
return v___x_1918_;
}
}
}
v___jp_1919_:
{
uint8_t v___x_1920_; 
v___x_1920_ = l_Lean_Expr_isMVar(v_r_1913_);
if (v___x_1920_ == 0)
{
v___y_1915_ = v___x_1920_;
goto v___jp_1914_;
}
else
{
uint8_t v___x_1921_; 
v___x_1921_ = l_Lean_Expr_hasLooseBVars(v___x_1897_);
v___y_1915_ = v___x_1921_;
goto v___jp_1914_;
}
}
v___jp_1922_:
{
if (v___y_1923_ == 0)
{
lean_dec_ref(v_l_1912_);
goto v___jp_1919_;
}
else
{
uint8_t v___x_1924_; 
v___x_1924_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_xs_1850_, v_l_1912_);
lean_dec_ref(v_l_1912_);
if (v___x_1924_ == 0)
{
goto v___jp_1919_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec_ref(v_r_1913_);
lean_dec_ref(v___x_1898_);
lean_dec_ref(v___x_1897_);
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_1929_; lean_object* v_body_1930_; 
v_binderType_1929_ = lean_ctor_get(v_e_1851_, 1);
v_body_1930_ = lean_ctor_get(v_e_1851_, 2);
v_ty_1858_ = v_binderType_1929_;
v_b_1859_ = v_body_1930_;
v___y_1860_ = v_a_1852_;
v___y_1861_ = v_a_1853_;
v___y_1862_ = v_a_1854_;
v___y_1863_ = v_a_1855_;
goto v___jp_1857_;
}
case 7:
{
lean_object* v_binderType_1931_; lean_object* v_body_1932_; 
v_binderType_1931_ = lean_ctor_get(v_e_1851_, 1);
v_body_1932_ = lean_ctor_get(v_e_1851_, 2);
v_ty_1858_ = v_binderType_1931_;
v_b_1859_ = v_body_1932_;
v___y_1860_ = v_a_1852_;
v___y_1861_ = v_a_1853_;
v___y_1862_ = v_a_1854_;
v___y_1863_ = v_a_1855_;
goto v___jp_1857_;
}
case 8:
{
lean_object* v_type_1933_; lean_object* v_value_1934_; lean_object* v_body_1935_; lean_object* v___x_1936_; 
v_type_1933_ = lean_ctor_get(v_e_1851_, 1);
v_value_1934_ = lean_ctor_get(v_e_1851_, 2);
v_body_1935_ = lean_ctor_get(v_e_1851_, 3);
v___x_1936_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1850_, v_type_1933_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1850_, v_value_1934_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref(v___x_1938_);
v___x_1940_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1850_, v_body_1935_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1950_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1950_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1950_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1945_ = lean_nat_add(v_a_1937_, v_a_1939_);
lean_dec(v_a_1939_);
lean_dec(v_a_1937_);
v___x_1946_ = lean_nat_add(v___x_1945_, v_a_1941_);
lean_dec(v_a_1941_);
lean_dec(v___x_1945_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1946_);
v___x_1948_ = v___x_1943_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
else
{
lean_dec(v_a_1939_);
lean_dec(v_a_1937_);
return v___x_1940_;
}
}
else
{
lean_dec(v_a_1937_);
return v___x_1938_;
}
}
else
{
return v___x_1936_;
}
}
case 10:
{
lean_object* v_expr_1951_; 
v_expr_1951_ = lean_ctor_get(v_e_1851_, 1);
v_e_1851_ = v_expr_1951_;
goto _start;
}
case 11:
{
lean_object* v_struct_1953_; 
v_struct_1953_ = lean_ctor_get(v_e_1851_, 2);
v_e_1851_ = v_struct_1953_;
goto _start;
}
default: 
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
return v___x_1956_;
}
}
}
v___jp_1857_:
{
lean_object* v___x_1864_; 
v___x_1864_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1850_, v_ty_1858_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1866_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
v___x_1866_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1850_, v_b_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1875_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1875_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1875_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1871_ = lean_nat_add(v_a_1865_, v_a_1867_);
lean_dec(v_a_1867_);
lean_dec(v_a_1865_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1871_);
v___x_1873_ = v___x_1869_;
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
else
{
lean_dec(v_a_1865_);
return v___x_1866_;
}
}
else
{
return v___x_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___boxed(lean_object* v_xs_1957_, lean_object* v_e_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1957_, v_e_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec_ref(v_e_1958_);
lean_dec_ref(v_xs_1957_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(lean_object* v_xs_1965_, lean_object* v_e_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1965_, v_e_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars___boxed(lean_object* v_xs_1973_, lean_object* v_e_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(v_xs_1973_, v_e_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec_ref(v_e_1974_);
lean_dec_ref(v_xs_1973_);
return v_res_1980_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig(void){
_start:
{
lean_object* v___x_1981_; lean_object* v_config_1982_; uint8_t v_foApprox_1983_; uint8_t v_ctxApprox_1984_; uint8_t v_quasiPatternApprox_1985_; uint8_t v_constApprox_1986_; uint8_t v_isDefEqStuckEx_1987_; uint8_t v_unificationHints_1988_; uint8_t v_proofIrrelevance_1989_; uint8_t v_assignSyntheticOpaque_1990_; uint8_t v_offsetCnstrs_1991_; uint8_t v_transparency_1992_; uint8_t v_etaStruct_1993_; uint8_t v_univApprox_1994_; uint8_t v_zetaUnused_1995_; uint8_t v_zetaHave_1996_; uint8_t v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1981_ = l_Lean_Meta_simpGlobalConfig;
v_config_1982_ = lean_ctor_get(v___x_1981_, 0);
v_foApprox_1983_ = lean_ctor_get_uint8(v_config_1982_, 0);
v_ctxApprox_1984_ = lean_ctor_get_uint8(v_config_1982_, 1);
v_quasiPatternApprox_1985_ = lean_ctor_get_uint8(v_config_1982_, 2);
v_constApprox_1986_ = lean_ctor_get_uint8(v_config_1982_, 3);
v_isDefEqStuckEx_1987_ = lean_ctor_get_uint8(v_config_1982_, 4);
v_unificationHints_1988_ = lean_ctor_get_uint8(v_config_1982_, 5);
v_proofIrrelevance_1989_ = lean_ctor_get_uint8(v_config_1982_, 6);
v_assignSyntheticOpaque_1990_ = lean_ctor_get_uint8(v_config_1982_, 7);
v_offsetCnstrs_1991_ = lean_ctor_get_uint8(v_config_1982_, 8);
v_transparency_1992_ = lean_ctor_get_uint8(v_config_1982_, 9);
v_etaStruct_1993_ = lean_ctor_get_uint8(v_config_1982_, 10);
v_univApprox_1994_ = lean_ctor_get_uint8(v_config_1982_, 11);
v_zetaUnused_1995_ = lean_ctor_get_uint8(v_config_1982_, 17);
v_zetaHave_1996_ = lean_ctor_get_uint8(v_config_1982_, 18);
v___x_1997_ = 1;
v___x_1998_ = 2;
v___x_1999_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1999_, 0, v_foApprox_1983_);
lean_ctor_set_uint8(v___x_1999_, 1, v_ctxApprox_1984_);
lean_ctor_set_uint8(v___x_1999_, 2, v_quasiPatternApprox_1985_);
lean_ctor_set_uint8(v___x_1999_, 3, v_constApprox_1986_);
lean_ctor_set_uint8(v___x_1999_, 4, v_isDefEqStuckEx_1987_);
lean_ctor_set_uint8(v___x_1999_, 5, v_unificationHints_1988_);
lean_ctor_set_uint8(v___x_1999_, 6, v_proofIrrelevance_1989_);
lean_ctor_set_uint8(v___x_1999_, 7, v_assignSyntheticOpaque_1990_);
lean_ctor_set_uint8(v___x_1999_, 8, v_offsetCnstrs_1991_);
lean_ctor_set_uint8(v___x_1999_, 9, v_transparency_1992_);
lean_ctor_set_uint8(v___x_1999_, 10, v_etaStruct_1993_);
lean_ctor_set_uint8(v___x_1999_, 11, v_univApprox_1994_);
lean_ctor_set_uint8(v___x_1999_, 12, v___x_1997_);
lean_ctor_set_uint8(v___x_1999_, 13, v___x_1997_);
lean_ctor_set_uint8(v___x_1999_, 14, v___x_1998_);
lean_ctor_set_uint8(v___x_1999_, 15, v___x_1997_);
lean_ctor_set_uint8(v___x_1999_, 16, v___x_1997_);
lean_ctor_set_uint8(v___x_1999_, 17, v_zetaUnused_1995_);
lean_ctor_set_uint8(v___x_1999_, 18, v_zetaHave_1996_);
v___x_2000_ = l_Lean_Meta_Config_toConfigWithKey(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(lean_object* v_k_2001_, uint8_t v_allowLevelAssignments_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2002_, v_k_2001_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
v_a_2017_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2008_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2008_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg___boxed(lean_object* v_k_2025_, lean_object* v_allowLevelAssignments_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2032_; lean_object* v_res_2033_; 
v_allowLevelAssignments_boxed_2032_ = lean_unbox(v_allowLevelAssignments_2026_);
v_res_2033_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_2025_, v_allowLevelAssignments_boxed_2032_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(lean_object* v_00_u03b1_2034_, lean_object* v_k_2035_, uint8_t v_allowLevelAssignments_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_2035_, v_allowLevelAssignments_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___boxed(lean_object* v_00_u03b1_2043_, lean_object* v_k_2044_, lean_object* v_allowLevelAssignments_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2051_; lean_object* v_res_2052_; 
v_allowLevelAssignments_boxed_2051_ = lean_unbox(v_allowLevelAssignments_2045_);
v_res_2052_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(v_00_u03b1_2043_, v_k_2044_, v_allowLevelAssignments_boxed_2051_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
return v_res_2052_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2060_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v___x_2063_);
return v___x_2065_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_unsigned_to_nat(32u);
v___x_2067_ = lean_mk_empty_array_with_capacity(v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8(void){
_start:
{
size_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2069_ = ((size_t)5ULL);
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = lean_unsigned_to_nat(32u);
v___x_2072_ = lean_mk_empty_array_with_capacity(v___x_2071_);
v___x_2073_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7);
v___x_2074_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v___x_2072_);
lean_ctor_set(v___x_2074_, 2, v___x_2070_);
lean_ctor_set(v___x_2074_, 3, v___x_2070_);
lean_ctor_set_usize(v___x_2074_, 4, v___x_2069_);
return v___x_2074_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8);
v___x_2076_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5);
v___x_2077_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
lean_ctor_set(v___x_2077_, 2, v___x_2076_);
lean_ctor_set(v___x_2077_, 3, v___x_2075_);
return v___x_2077_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9);
v___x_2079_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___x_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(lean_object* v_a_2081_, lean_object* v_xs_2082_, lean_object* v_b_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_snd_2089_; lean_object* v_snd_2090_; lean_object* v_snd_2091_; lean_object* v_fst_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2219_; 
v_snd_2089_ = lean_ctor_get(v_b_2083_, 1);
lean_inc(v_snd_2089_);
v_snd_2090_ = lean_ctor_get(v_snd_2089_, 1);
lean_inc(v_snd_2090_);
v_snd_2091_ = lean_ctor_get(v_snd_2090_, 1);
lean_inc(v_snd_2091_);
v_fst_2092_ = lean_ctor_get(v_b_2083_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_b_2083_);
if (v_isSharedCheck_2219_ == 0)
{
lean_object* v_unused_2220_; 
v_unused_2220_ = lean_ctor_get(v_b_2083_, 1);
lean_dec(v_unused_2220_);
v___x_2094_ = v_b_2083_;
v_isShared_2095_ = v_isSharedCheck_2219_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_fst_2092_);
lean_dec(v_b_2083_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2219_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_fst_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2217_; 
v_fst_2096_ = lean_ctor_get(v_snd_2089_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_snd_2089_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; 
v_unused_2218_ = lean_ctor_get(v_snd_2089_, 1);
lean_dec(v_unused_2218_);
v___x_2098_ = v_snd_2089_;
v_isShared_2099_ = v_isSharedCheck_2217_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_fst_2096_);
lean_dec(v_snd_2089_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2217_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_fst_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2215_; 
v_fst_2100_ = lean_ctor_get(v_snd_2090_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_snd_2090_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; 
v_unused_2216_ = lean_ctor_get(v_snd_2090_, 1);
lean_dec(v_unused_2216_);
v___x_2102_ = v_snd_2090_;
v_isShared_2103_ = v_isSharedCheck_2215_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_fst_2100_);
lean_dec(v_snd_2090_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2215_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_fst_2104_; lean_object* v_snd_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2214_; 
v_fst_2104_ = lean_ctor_get(v_snd_2091_, 0);
v_snd_2105_ = lean_ctor_get(v_snd_2091_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_snd_2091_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2107_ = v_snd_2091_;
v_isShared_2108_ = v_isSharedCheck_2214_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_snd_2105_);
lean_inc(v_fst_2104_);
lean_dec(v_snd_2091_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2214_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2109_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__2));
v___x_2110_ = lean_unsigned_to_nat(3u);
v___x_2111_ = l_Lean_Expr_isAppOfArity(v_fst_2092_, v___x_2109_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2113_; 
lean_dec_ref(v_a_2081_);
if (v_isShared_2108_ == 0)
{
v___x_2113_ = v___x_2107_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_fst_2104_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_snd_2105_);
v___x_2113_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 1, v___x_2113_);
v___x_2115_ = v___x_2102_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_fst_2100_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2117_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v___x_2115_);
v___x_2117_ = v___x_2098_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_fst_2096_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2119_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 1, v___x_2117_);
v___x_2119_ = v___x_2094_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_fst_2092_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
}
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_del_object(v___x_2094_);
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = l_Lean_Expr_getAppNumArgs(v_fst_2092_);
v___x_2127_ = lean_nat_sub(v___x_2126_, v___x_2125_);
v___x_2128_ = lean_nat_sub(v___x_2127_, v___x_2125_);
lean_dec(v___x_2127_);
v___x_2129_ = l_Lean_Expr_getRevArg_x21(v_fst_2092_, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = 0;
v___x_2132_ = lean_box(0);
v___x_2133_ = l_Lean_Meta_mkFreshExprMVar(v___x_2130_, v___x_2131_, v___x_2132_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref(v___x_2133_);
v___x_2135_ = lean_mk_empty_array_with_capacity(v___x_2125_);
v___x_2136_ = lean_array_push(v___x_2135_, v_a_2134_);
v___x_2137_ = l_Lean_Expr_beta(v_fst_2096_, v___x_2136_);
v___x_2138_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__3));
v___x_2139_ = lean_box(0);
v___x_2140_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10);
lean_inc_ref(v_a_2081_);
v___x_2141_ = l_Lean_Meta_simp(v___x_2137_, v_a_2081_, v___x_2138_, v___x_2139_, v___x_2140_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v_fst_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2196_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v___x_2141_);
v_fst_2143_ = lean_ctor_get(v_a_2142_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_a_2142_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v_a_2142_, 1);
lean_dec(v_unused_2197_);
v___x_2145_ = v_a_2142_;
v_isShared_2146_ = v_isSharedCheck_2196_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_fst_2143_);
lean_dec(v_a_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2196_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v_expr_2147_; lean_object* v___x_2148_; 
v_expr_2147_ = lean_ctor_get(v_fst_2143_, 0);
lean_inc_ref(v_expr_2147_);
lean_dec(v_fst_2143_);
v___x_2148_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2082_, v_expr_2147_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v_lastSuccess_2152_; lean_object* v_boundAssignments_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; uint8_t v___x_2185_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
v___x_2150_ = lean_nat_add(v_fst_2100_, v___x_2125_);
lean_dec(v_fst_2100_);
v___x_2185_ = lean_nat_dec_lt(v_a_2149_, v_snd_2105_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = l_Lean_Expr_getAppFn_x27(v_expr_2147_);
v___x_2187_ = l_Lean_Expr_isMVar(v___x_2186_);
lean_dec_ref(v___x_2186_);
if (v___x_2187_ == 0)
{
lean_dec(v_a_2149_);
v_lastSuccess_2152_ = v_fst_2104_;
v_boundAssignments_2153_ = v_snd_2105_;
v___y_2154_ = v___y_2084_;
v___y_2155_ = v___y_2085_;
v___y_2156_ = v___y_2086_;
v___y_2157_ = v___y_2087_;
goto v___jp_2151_;
}
else
{
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_inc(v___x_2150_);
v_lastSuccess_2152_ = v___x_2150_;
v_boundAssignments_2153_ = v_a_2149_;
v___y_2154_ = v___y_2084_;
v___y_2155_ = v___y_2085_;
v___y_2156_ = v___y_2086_;
v___y_2157_ = v___y_2087_;
goto v___jp_2151_;
}
}
else
{
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_inc(v___x_2150_);
v_lastSuccess_2152_ = v___x_2150_;
v_boundAssignments_2153_ = v_a_2149_;
v___y_2154_ = v___y_2084_;
v___y_2155_ = v___y_2085_;
v___y_2156_ = v___y_2086_;
v___y_2157_ = v___y_2087_;
goto v___jp_2151_;
}
v___jp_2151_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2158_ = lean_unsigned_to_nat(2u);
v___x_2159_ = lean_nat_sub(v___x_2126_, v___x_2158_);
lean_dec(v___x_2126_);
v___x_2160_ = lean_nat_sub(v___x_2159_, v___x_2125_);
lean_dec(v___x_2159_);
v___x_2161_ = l_Lean_Expr_getRevArg_x21(v_fst_2092_, v___x_2160_);
lean_dec(v_fst_2092_);
v___x_2162_ = l_Lean_Meta_whnfR(v___x_2161_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___x_2162_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 1, v_boundAssignments_2153_);
lean_ctor_set(v___x_2145_, 0, v_lastSuccess_2152_);
v___x_2165_ = v___x_2145_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_lastSuccess_2152_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_boundAssignments_2153_);
v___x_2165_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 1, v___x_2165_);
lean_ctor_set(v___x_2107_, 0, v___x_2150_);
v___x_2167_ = v___x_2107_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 1, v___x_2167_);
lean_ctor_set(v___x_2102_, 0, v_expr_2147_);
v___x_2169_ = v___x_2102_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_expr_2147_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2171_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v___x_2169_);
lean_ctor_set(v___x_2098_, 0, v_a_2163_);
v___x_2171_ = v___x_2098_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2163_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
v_b_2083_ = v___x_2171_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_boundAssignments_2153_);
lean_dec(v_lastSuccess_2152_);
lean_dec(v___x_2150_);
lean_dec_ref(v_expr_2147_);
lean_del_object(v___x_2145_);
lean_del_object(v___x_2107_);
lean_del_object(v___x_2102_);
lean_del_object(v___x_2098_);
lean_dec_ref(v_a_2081_);
v_a_2177_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2162_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2162_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v_expr_2147_);
lean_del_object(v___x_2145_);
lean_dec(v___x_2126_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_del_object(v___x_2102_);
lean_dec(v_fst_2100_);
lean_del_object(v___x_2098_);
lean_dec(v_fst_2092_);
lean_dec_ref(v_a_2081_);
v_a_2188_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2148_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2148_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v___x_2126_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_del_object(v___x_2102_);
lean_dec(v_fst_2100_);
lean_del_object(v___x_2098_);
lean_dec(v_fst_2092_);
lean_dec_ref(v_a_2081_);
v_a_2198_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2141_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2141_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v___x_2126_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_del_object(v___x_2102_);
lean_dec(v_fst_2100_);
lean_del_object(v___x_2098_);
lean_dec(v_fst_2096_);
lean_dec(v_fst_2092_);
lean_dec_ref(v_a_2081_);
v_a_2206_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2133_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2133_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___boxed(lean_object* v_a_2221_, lean_object* v_xs_2222_, lean_object* v_b_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(v_a_2221_, v_xs_2222_, v_b_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_xs_2222_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(lean_object* v___x_2230_, uint8_t v___x_2231_, lean_object* v_00_u03c3s_2232_, lean_object* v_xs_2233_, lean_object* v_e_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
if (v___x_2231_ == 0)
{
lean_object* v_config_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2314_; 
v_config_2240_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2242_ = v___x_2230_;
v_isShared_2243_ = v_isSharedCheck_2314_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_config_2240_);
lean_dec(v___x_2230_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2314_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
uint8_t v_trackZetaDelta_2244_; lean_object* v_zetaDeltaSet_2245_; lean_object* v_lctx_2246_; lean_object* v_localInstances_2247_; lean_object* v_defEqCtx_x3f_2248_; lean_object* v_synthPendingDepth_2249_; lean_object* v_canUnfold_x3f_2250_; uint8_t v_univApprox_2251_; uint8_t v_inTypeClassResolution_2252_; uint8_t v_cacheInferType_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2312_; 
v_trackZetaDelta_2244_ = lean_ctor_get_uint8(v___y_2235_, sizeof(void*)*7);
v_zetaDeltaSet_2245_ = lean_ctor_get(v___y_2235_, 1);
v_lctx_2246_ = lean_ctor_get(v___y_2235_, 2);
v_localInstances_2247_ = lean_ctor_get(v___y_2235_, 3);
v_defEqCtx_x3f_2248_ = lean_ctor_get(v___y_2235_, 4);
v_synthPendingDepth_2249_ = lean_ctor_get(v___y_2235_, 5);
v_canUnfold_x3f_2250_ = lean_ctor_get(v___y_2235_, 6);
v_univApprox_2251_ = lean_ctor_get_uint8(v___y_2235_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2252_ = lean_ctor_get_uint8(v___y_2235_, sizeof(void*)*7 + 2);
v_cacheInferType_2253_ = lean_ctor_get_uint8(v___y_2235_, sizeof(void*)*7 + 3);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___y_2235_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; 
v_unused_2313_ = lean_ctor_get(v___y_2235_, 0);
lean_dec(v_unused_2313_);
v___x_2255_ = v___y_2235_;
v_isShared_2256_ = v_isSharedCheck_2312_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_canUnfold_x3f_2250_);
lean_inc(v_synthPendingDepth_2249_);
lean_inc(v_defEqCtx_x3f_2248_);
lean_inc(v_localInstances_2247_);
lean_inc(v_lctx_2246_);
lean_inc(v_zetaDeltaSet_2245_);
lean_dec(v___y_2235_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2312_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
uint64_t v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2240_);
if (v_isShared_2243_ == 0)
{
v___x_2259_ = v___x_2242_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_config_2240_);
v___x_2259_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2261_; 
lean_ctor_set_uint64(v___x_2259_, sizeof(void*)*1, v___x_2257_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2259_);
v___x_2261_ = v___x_2255_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_zetaDeltaSet_2245_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_lctx_2246_);
lean_ctor_set(v_reuseFailAlloc_2310_, 3, v_localInstances_2247_);
lean_ctor_set(v_reuseFailAlloc_2310_, 4, v_defEqCtx_x3f_2248_);
lean_ctor_set(v_reuseFailAlloc_2310_, 5, v_synthPendingDepth_2249_);
lean_ctor_set(v_reuseFailAlloc_2310_, 6, v_canUnfold_x3f_2250_);
lean_ctor_set_uint8(v_reuseFailAlloc_2310_, sizeof(void*)*7, v_trackZetaDelta_2244_);
lean_ctor_set_uint8(v_reuseFailAlloc_2310_, sizeof(void*)*7 + 1, v_univApprox_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2310_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2252_);
lean_ctor_set_uint8(v_reuseFailAlloc_2310_, sizeof(void*)*7 + 3, v_cacheInferType_2253_);
v___x_2261_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v___x_2261_, v___y_2237_, v___y_2238_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref(v___x_2262_);
v___x_2264_ = l_Lean_Meta_whnfR(v_00_u03c3s_2232_, v___x_2261_, v___y_2236_, v___y_2237_, v___y_2238_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref(v___x_2264_);
v___x_2266_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2233_, v_e_2234_, v___x_2261_, v___y_2236_, v___y_2237_, v___y_2238_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v_a_2267_);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2271_, 0, v_e_2234_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2272_, 0, v_a_2265_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(v_a_2263_, v_xs_2233_, v___x_2272_, v___x_2261_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec_ref(v___x_2261_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2285_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2285_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2285_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v_snd_2278_; lean_object* v_snd_2279_; lean_object* v_snd_2280_; lean_object* v_fst_2281_; lean_object* v___x_2283_; 
v_snd_2278_ = lean_ctor_get(v_a_2274_, 1);
lean_inc(v_snd_2278_);
lean_dec(v_a_2274_);
v_snd_2279_ = lean_ctor_get(v_snd_2278_, 1);
lean_inc(v_snd_2279_);
lean_dec(v_snd_2278_);
v_snd_2280_ = lean_ctor_get(v_snd_2279_, 1);
lean_inc(v_snd_2280_);
lean_dec(v_snd_2279_);
v_fst_2281_ = lean_ctor_get(v_snd_2280_, 0);
lean_inc(v_fst_2281_);
lean_dec(v_snd_2280_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v_fst_2281_);
v___x_2283_ = v___x_2276_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_fst_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
v_a_2286_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2273_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2273_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_dec(v_a_2265_);
lean_dec(v_a_2263_);
lean_dec_ref(v___x_2261_);
lean_dec_ref(v_e_2234_);
return v___x_2266_;
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v_a_2263_);
lean_dec_ref(v___x_2261_);
lean_dec_ref(v_e_2234_);
v_a_2294_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2264_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2264_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec_ref(v___x_2261_);
lean_dec_ref(v_e_2234_);
lean_dec_ref(v_00_u03c3s_2232_);
v_a_2302_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2262_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2262_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_e_2234_);
lean_dec_ref(v_00_u03c3s_2232_);
lean_dec_ref(v___x_2230_);
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed(lean_object* v___x_2317_, lean_object* v___x_2318_, lean_object* v_00_u03c3s_2319_, lean_object* v_xs_2320_, lean_object* v_e_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v___x_4178__boxed_2327_; lean_object* v_res_2328_; 
v___x_4178__boxed_2327_ = lean_unbox(v___x_2318_);
v_res_2328_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(v___x_2317_, v___x_4178__boxed_2327_, v_00_u03c3s_2319_, v_xs_2320_, v_e_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v_xs_2320_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(lean_object* v_xs_2329_, lean_object* v_00_u03c3s_2330_, lean_object* v_e_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___f_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; 
v___x_2337_ = l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig;
v___x_2338_ = lean_array_get_size(v_xs_2329_);
v___x_2339_ = lean_unsigned_to_nat(0u);
v___x_2340_ = lean_nat_dec_eq(v___x_2338_, v___x_2339_);
v___x_2341_ = lean_box(v___x_2340_);
v___f_2342_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2342_, 0, v___x_2337_);
lean_closure_set(v___f_2342_, 1, v___x_2341_);
lean_closure_set(v___f_2342_, 2, v_00_u03c3s_2330_);
lean_closure_set(v___f_2342_, 3, v_xs_2329_);
lean_closure_set(v___f_2342_, 4, v_e_2331_);
v___x_2343_ = 0;
v___x_2344_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_2342_, v___x_2343_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___boxed(lean_object* v_xs_2345_, lean_object* v_00_u03c3s_2346_, lean_object* v_e_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_xs_2345_, v_00_u03c3s_2346_, v_e_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
return v_res_2353_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0));
v___x_2356_ = l_Lean_stringToMessageData(v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(lean_object* v_a_2370_, lean_object* v___x_2371_, uint8_t v___x_2372_, lean_object* v___x_2373_, lean_object* v_proof_2374_, lean_object* v_prio_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v_config_2382_; uint8_t v_trackZetaDelta_2383_; lean_object* v_zetaDeltaSet_2384_; lean_object* v_lctx_2385_; lean_object* v_localInstances_2386_; lean_object* v_defEqCtx_x3f_2387_; lean_object* v_synthPendingDepth_2388_; lean_object* v_canUnfold_x3f_2389_; uint8_t v_univApprox_2390_; uint8_t v_inTypeClassResolution_2391_; uint8_t v_cacheInferType_2392_; uint64_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2381_ = l_Lean_Meta_simpGlobalConfig;
v_config_2382_ = lean_ctor_get(v___x_2381_, 0);
v_trackZetaDelta_2383_ = lean_ctor_get_uint8(v___y_2376_, sizeof(void*)*7);
v_zetaDeltaSet_2384_ = lean_ctor_get(v___y_2376_, 1);
v_lctx_2385_ = lean_ctor_get(v___y_2376_, 2);
v_localInstances_2386_ = lean_ctor_get(v___y_2376_, 3);
v_defEqCtx_x3f_2387_ = lean_ctor_get(v___y_2376_, 4);
v_synthPendingDepth_2388_ = lean_ctor_get(v___y_2376_, 5);
v_canUnfold_x3f_2389_ = lean_ctor_get(v___y_2376_, 6);
v_univApprox_2390_ = lean_ctor_get_uint8(v___y_2376_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2391_ = lean_ctor_get_uint8(v___y_2376_, sizeof(void*)*7 + 2);
v_cacheInferType_2392_ = lean_ctor_get_uint8(v___y_2376_, sizeof(void*)*7 + 3);
v___x_2393_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2382_);
lean_inc_ref(v_config_2382_);
v___x_2394_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2394_, 0, v_config_2382_);
lean_ctor_set_uint64(v___x_2394_, sizeof(void*)*1, v___x_2393_);
lean_inc(v_canUnfold_x3f_2389_);
lean_inc(v_synthPendingDepth_2388_);
lean_inc(v_defEqCtx_x3f_2387_);
lean_inc_ref(v_localInstances_2386_);
lean_inc_ref(v_lctx_2385_);
lean_inc(v_zetaDeltaSet_2384_);
v___x_2395_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
lean_ctor_set(v___x_2395_, 1, v_zetaDeltaSet_2384_);
lean_ctor_set(v___x_2395_, 2, v_lctx_2385_);
lean_ctor_set(v___x_2395_, 3, v_localInstances_2386_);
lean_ctor_set(v___x_2395_, 4, v_defEqCtx_x3f_2387_);
lean_ctor_set(v___x_2395_, 5, v_synthPendingDepth_2388_);
lean_ctor_set(v___x_2395_, 6, v_canUnfold_x3f_2389_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*7, v_trackZetaDelta_2383_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*7 + 1, v_univApprox_2390_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2391_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*7 + 3, v_cacheInferType_2392_);
v___x_2396_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2370_, v___x_2371_, v___x_2372_, v___x_2395_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec_ref(v___x_2395_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v_snd_2398_; lean_object* v_fst_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2500_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref(v___x_2396_);
v_snd_2398_ = lean_ctor_get(v_a_2397_, 1);
v_fst_2399_ = lean_ctor_get(v_a_2397_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_a_2397_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2401_ = v_a_2397_;
v_isShared_2402_ = v_isSharedCheck_2500_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_snd_2398_);
lean_inc(v_fst_2399_);
lean_dec(v_a_2397_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2500_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v_snd_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2498_; 
v_snd_2403_ = lean_ctor_get(v_snd_2398_, 1);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_snd_2398_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; 
v_unused_2499_ = lean_ctor_get(v_snd_2398_, 0);
lean_dec(v_unused_2499_);
v___x_2405_ = v_snd_2398_;
v_isShared_2406_ = v_isSharedCheck_2498_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_snd_2403_);
lean_dec(v_snd_2398_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2498_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_Meta_whnfR(v_snd_2403_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc_n(v_a_2408_, 2);
lean_dec_ref(v___x_2407_);
v___x_2420_ = l_Lean_Expr_cleanupAnnotations(v_a_2408_);
v___x_2421_ = l_Lean_Expr_isApp(v___x_2420_);
if (v___x_2421_ == 0)
{
lean_dec_ref(v___x_2420_);
lean_del_object(v___x_2401_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v___y_2410_ = v___y_2376_;
v___y_2411_ = v___y_2377_;
v___y_2412_ = v___y_2378_;
v___y_2413_ = v___y_2379_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2420_);
v___x_2423_ = l_Lean_Expr_isApp(v___x_2422_);
if (v___x_2423_ == 0)
{
lean_dec_ref(v___x_2422_);
lean_del_object(v___x_2401_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v___y_2410_ = v___y_2376_;
v___y_2411_ = v___y_2377_;
v___y_2412_ = v___y_2378_;
v___y_2413_ = v___y_2379_;
goto v___jp_2409_;
}
else
{
lean_object* v_arg_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
v_arg_2424_ = lean_ctor_get(v___x_2422_, 1);
lean_inc_ref(v_arg_2424_);
v___x_2425_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2422_);
v___x_2426_ = l_Lean_Expr_isApp(v___x_2425_);
if (v___x_2426_ == 0)
{
lean_dec_ref(v___x_2425_);
lean_dec_ref(v_arg_2424_);
lean_del_object(v___x_2401_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v___y_2410_ = v___y_2376_;
v___y_2411_ = v___y_2377_;
v___y_2412_ = v___y_2378_;
v___y_2413_ = v___y_2379_;
goto v___jp_2409_;
}
else
{
lean_object* v_arg_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v_arg_2427_ = lean_ctor_get(v___x_2425_, 1);
lean_inc_ref(v_arg_2427_);
v___x_2428_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2425_);
v___x_2429_ = l_Lean_Expr_isApp(v___x_2428_);
if (v___x_2429_ == 0)
{
lean_dec_ref(v___x_2428_);
lean_dec_ref(v_arg_2427_);
lean_dec_ref(v_arg_2424_);
lean_del_object(v___x_2401_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v___y_2410_ = v___y_2376_;
v___y_2411_ = v___y_2377_;
v___y_2412_ = v___y_2378_;
v___y_2413_ = v___y_2379_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2430_; uint8_t v___x_2431_; 
v___x_2430_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2428_);
v___x_2431_ = l_Lean_Expr_isApp(v___x_2430_);
if (v___x_2431_ == 0)
{
lean_dec_ref(v___x_2430_);
lean_dec_ref(v_arg_2427_);
lean_dec_ref(v_arg_2424_);
lean_del_object(v___x_2401_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v___y_2410_ = v___y_2376_;
v___y_2411_ = v___y_2377_;
v___y_2412_ = v___y_2378_;
v___y_2413_ = v___y_2379_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2430_);
v___x_2433_ = l_Lean_Expr_isApp(v___x_2432_);
if (v___x_2433_ == 0)
{
lean_dec_ref(v___x_2432_);
lean_dec_ref(v_arg_2427_);
lean_dec_ref(v_arg_2424_);
lean_del_object(v___x_2401_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v___y_2410_ = v___y_2376_;
v___y_2411_ = v___y_2377_;
v___y_2412_ = v___y_2378_;
v___y_2413_ = v___y_2379_;
goto v___jp_2409_;
}
else
{
lean_object* v_arg_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v_arg_2434_ = lean_ctor_get(v___x_2432_, 1);
lean_inc_ref(v_arg_2434_);
v___x_2435_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2432_);
v___x_2436_ = l_Lean_Expr_isApp(v___x_2435_);
if (v___x_2436_ == 0)
{
lean_dec_ref(v___x_2435_);
lean_dec_ref(v_arg_2434_);
lean_dec_ref(v_arg_2427_);
lean_dec_ref(v_arg_2424_);
lean_del_object(v___x_2401_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v___y_2410_ = v___y_2376_;
v___y_2411_ = v___y_2377_;
v___y_2412_ = v___y_2378_;
v___y_2413_ = v___y_2379_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2437_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2435_);
v___x_2438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4));
v___x_2439_ = l_Lean_Expr_isConstOf(v___x_2437_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_dec_ref(v___x_2437_);
lean_dec_ref(v_arg_2434_);
lean_dec_ref(v_arg_2427_);
lean_dec_ref(v_arg_2424_);
lean_del_object(v___x_2401_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v___y_2410_ = v___y_2376_;
v___y_2411_ = v___y_2377_;
v___y_2412_ = v___y_2378_;
v___y_2413_ = v___y_2379_;
goto v___jp_2409_;
}
else
{
uint8_t v___x_2440_; lean_object* v___x_2441_; 
lean_dec(v_a_2408_);
lean_del_object(v___x_2405_);
v___x_2440_ = 0;
lean_inc_ref(v_arg_2427_);
v___x_2441_ = l_Lean_Meta_DiscrTree_mkPath(v_arg_2427_, v___x_2440_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref(v___x_2441_);
v___x_2443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7));
v___x_2444_ = l_Lean_Expr_constLevels_x21(v___x_2437_);
lean_dec_ref(v___x_2437_);
v___x_2445_ = lean_unsigned_to_nat(0u);
v___x_2446_ = l_List_get_x21Internal___redArg(v___x_2373_, v___x_2444_, v___x_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
if (v_isShared_2402_ == 0)
{
lean_ctor_set_tag(v___x_2401_, 1);
lean_ctor_set(v___x_2401_, 1, v___x_2447_);
lean_ctor_set(v___x_2401_, 0, v___x_2446_);
v___x_2449_ = v___x_2401_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = l_Lean_mkConst(v___x_2443_, v___x_2449_);
v___x_2451_ = l_Lean_Expr_app___override(v___x_2450_, v_arg_2434_);
lean_inc(v_fst_2399_);
v___x_2452_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_fst_2399_, v___x_2451_, v_arg_2424_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; uint8_t v___x_2454_; lean_object* v___x_2455_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref(v___x_2452_);
v___x_2454_ = 1;
v___x_2455_ = l_Lean_Meta_mkForallFVars(v_fst_2399_, v_arg_2427_, v___x_2440_, v___x_2439_, v___x_2439_, v___x_2454_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v_fst_2399_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2464_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2464_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2464_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2460_, 0, v_a_2442_);
lean_ctor_set(v___x_2460_, 1, v_a_2456_);
lean_ctor_set(v___x_2460_, 2, v_proof_2374_);
lean_ctor_set(v___x_2460_, 3, v_a_2453_);
lean_ctor_set(v___x_2460_, 4, v_prio_2375_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2460_);
v___x_2462_ = v___x_2458_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_2453_);
lean_dec(v_a_2442_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v_a_2465_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2455_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2455_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v_a_2442_);
lean_dec_ref(v_arg_2427_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v_a_2473_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2452_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2452_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
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
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec_ref(v___x_2437_);
lean_dec_ref(v_arg_2434_);
lean_dec_ref(v_arg_2427_);
lean_dec_ref(v_arg_2424_);
lean_del_object(v___x_2401_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v_a_2482_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2441_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2441_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
}
}
}
}
}
}
v___jp_2409_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2414_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1);
v___x_2415_ = l_Lean_indentExpr(v_a_2408_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set_tag(v___x_2405_, 7);
lean_ctor_set(v___x_2405_, 1, v___x_2415_);
lean_ctor_set(v___x_2405_, 0, v___x_2414_);
v___x_2417_ = v___x_2405_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2417_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_del_object(v___x_2405_);
lean_del_object(v___x_2401_);
lean_dec(v_fst_2399_);
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v_a_2490_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2407_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2407_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v_prio_2375_);
lean_dec_ref(v_proof_2374_);
v_a_2501_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2396_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2396_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed(lean_object* v_a_2509_, lean_object* v___x_2510_, lean_object* v___x_2511_, lean_object* v___x_2512_, lean_object* v_proof_2513_, lean_object* v_prio_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
uint8_t v___x_3664__boxed_2520_; lean_object* v_res_2521_; 
v___x_3664__boxed_2520_ = lean_unbox(v___x_2511_);
v_res_2521_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(v_a_2509_, v___x_2510_, v___x_3664__boxed_2520_, v___x_2512_, v_proof_2513_, v_prio_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___x_2512_);
return v_res_2521_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(lean_object* v_type_2525_, lean_object* v_proof_2526_, lean_object* v_prio_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v___x_2533_; lean_object* v_a_2534_; lean_object* v___x_2535_; 
v___x_2533_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_type_2525_, v_a_2529_);
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc_n(v_a_2534_, 2);
lean_dec_ref(v___x_2533_);
v___x_2535_ = l_Lean_Meta_isProp(v_a_2534_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2537_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; uint8_t v___x_2549_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref(v___x_2535_);
v___x_2537_ = lean_box(0);
v___x_2549_ = lean_unbox(v_a_2536_);
lean_dec(v_a_2536_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v_prio_2527_);
lean_dec_ref(v_proof_2526_);
v___x_2550_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1);
v___x_2551_ = l_Lean_indentExpr(v_a_2534_);
v___x_2552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2552_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
else
{
v___y_2539_ = v_a_2528_;
v___y_2540_ = v_a_2529_;
v___y_2541_ = v_a_2530_;
v___y_2542_ = v_a_2531_;
goto v___jp_2538_;
}
v___jp_2538_:
{
lean_object* v___x_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; lean_object* v___f_2546_; uint8_t v___x_2547_; lean_object* v___x_2548_; 
v___x_2543_ = lean_box(0);
v___x_2544_ = 0;
v___x_2545_ = lean_box(v___x_2544_);
v___f_2546_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2546_, 0, v_a_2534_);
lean_closure_set(v___f_2546_, 1, v___x_2543_);
lean_closure_set(v___f_2546_, 2, v___x_2545_);
lean_closure_set(v___f_2546_, 3, v___x_2537_);
lean_closure_set(v___f_2546_, 4, v_proof_2526_);
lean_closure_set(v___f_2546_, 5, v_prio_2527_);
v___x_2547_ = 0;
v___x_2548_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_2546_, v___x_2547_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
return v___x_2548_;
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v_a_2534_);
lean_dec(v_prio_2527_);
lean_dec_ref(v_proof_2526_);
v_a_2562_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2535_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2535_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___boxed(lean_object* v_type_2570_, lean_object* v_proof_2571_, lean_object* v_prio_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_type_2570_, v_proof_2571_, v_prio_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(lean_object* v_declName_2579_, lean_object* v_prio_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v___x_2586_; 
lean_inc(v_declName_2579_);
v___x_2586_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_2579_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref(v___x_2586_);
v___x_2588_ = l_Lean_ConstantInfo_levelParams(v_a_2587_);
lean_dec(v_a_2587_);
v___x_2589_ = lean_box(0);
v___x_2590_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_2588_, v___x_2589_);
lean_inc(v_declName_2579_);
v___x_2591_ = l_Lean_mkConst(v_declName_2579_, v___x_2590_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2592_ = lean_infer_type(v___x_2591_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref(v___x_2592_);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v_declName_2579_);
v___x_2595_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_2593_, v___x_2594_, v_prio_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
return v___x_2595_;
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_prio_2580_);
lean_dec(v_declName_2579_);
v_a_2596_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2592_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2592_);
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
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_prio_2580_);
lean_dec(v_declName_2579_);
v_a_2604_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2586_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2586_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst___boxed(lean_object* v_declName_2612_, lean_object* v_prio_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_2612_, v_prio_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
return v_res_2619_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0));
v___x_2622_ = l_Lean_stringToMessageData(v___x_2621_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(lean_object* v_fvar_2626_, lean_object* v_prio_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v___x_2633_; 
lean_inc(v_fvar_2626_);
v___x_2633_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvar_2626_, v_a_2628_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref(v___x_2633_);
if (lean_obj_tag(v_a_2634_) == 1)
{
lean_object* v_val_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2644_; 
v_val_2635_ = lean_ctor_get(v_a_2634_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_a_2634_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2637_ = v_a_2634_;
v_isShared_2638_ = v_isSharedCheck_2644_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_val_2635_);
lean_dec(v_a_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2644_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = l_Lean_LocalDecl_type(v_val_2635_);
lean_dec(v_val_2635_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v_fvar_2626_);
v___x_2641_ = v___x_2637_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_fvar_2626_);
v___x_2641_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; 
v___x_2642_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v___x_2639_, v___x_2641_, v_prio_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
return v___x_2642_;
}
}
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec(v_a_2634_);
lean_dec(v_prio_2627_);
v___x_2645_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1);
v___x_2646_ = l_Lean_MessageData_ofName(v_fvar_2626_);
v___x_2647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3);
v___x_2649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2647_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
v___x_2650_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2649_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
return v___x_2650_;
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v_prio_2627_);
lean_dec(v_fvar_2626_);
v_a_2651_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2633_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2633_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___boxed(lean_object* v_fvar_2659_, lean_object* v_prio_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvar_2659_, v_prio_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; lean_object* v_ngen_2670_; lean_object* v_namePrefix_2671_; lean_object* v_idx_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2701_; 
v___x_2669_ = lean_st_ref_get(v___y_2667_);
v_ngen_2670_ = lean_ctor_get(v___x_2669_, 2);
lean_inc_ref(v_ngen_2670_);
lean_dec(v___x_2669_);
v_namePrefix_2671_ = lean_ctor_get(v_ngen_2670_, 0);
v_idx_2672_ = lean_ctor_get(v_ngen_2670_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_ngen_2670_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2674_ = v_ngen_2670_;
v_isShared_2675_ = v_isSharedCheck_2701_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_idx_2672_);
lean_inc(v_namePrefix_2671_);
lean_dec(v_ngen_2670_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2701_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v_env_2677_; lean_object* v_nextMacroScope_2678_; lean_object* v_auxDeclNGen_2679_; lean_object* v_traceState_2680_; lean_object* v_cache_2681_; lean_object* v_messages_2682_; lean_object* v_infoState_2683_; lean_object* v_snapshotTasks_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2699_; 
v___x_2676_ = lean_st_ref_take(v___y_2667_);
v_env_2677_ = lean_ctor_get(v___x_2676_, 0);
v_nextMacroScope_2678_ = lean_ctor_get(v___x_2676_, 1);
v_auxDeclNGen_2679_ = lean_ctor_get(v___x_2676_, 3);
v_traceState_2680_ = lean_ctor_get(v___x_2676_, 4);
v_cache_2681_ = lean_ctor_get(v___x_2676_, 5);
v_messages_2682_ = lean_ctor_get(v___x_2676_, 6);
v_infoState_2683_ = lean_ctor_get(v___x_2676_, 7);
v_snapshotTasks_2684_ = lean_ctor_get(v___x_2676_, 8);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v___x_2676_, 2);
lean_dec(v_unused_2700_);
v___x_2686_ = v___x_2676_;
v_isShared_2687_ = v_isSharedCheck_2699_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_snapshotTasks_2684_);
lean_inc(v_infoState_2683_);
lean_inc(v_messages_2682_);
lean_inc(v_cache_2681_);
lean_inc(v_traceState_2680_);
lean_inc(v_auxDeclNGen_2679_);
lean_inc(v_nextMacroScope_2678_);
lean_inc(v_env_2677_);
lean_dec(v___x_2676_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2699_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_r_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2692_; 
lean_inc(v_idx_2672_);
lean_inc(v_namePrefix_2671_);
v_r_2688_ = l_Lean_Name_num___override(v_namePrefix_2671_, v_idx_2672_);
v___x_2689_ = lean_unsigned_to_nat(1u);
v___x_2690_ = lean_nat_add(v_idx_2672_, v___x_2689_);
lean_dec(v_idx_2672_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 1, v___x_2690_);
v___x_2692_ = v___x_2674_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_namePrefix_2671_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2694_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 2, v___x_2692_);
v___x_2694_ = v___x_2686_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_env_2677_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_nextMacroScope_2678_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2697_, 3, v_auxDeclNGen_2679_);
lean_ctor_set(v_reuseFailAlloc_2697_, 4, v_traceState_2680_);
lean_ctor_set(v_reuseFailAlloc_2697_, 5, v_cache_2681_);
lean_ctor_set(v_reuseFailAlloc_2697_, 6, v_messages_2682_);
lean_ctor_set(v_reuseFailAlloc_2697_, 7, v_infoState_2683_);
lean_ctor_set(v_reuseFailAlloc_2697_, 8, v_snapshotTasks_2684_);
v___x_2694_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = lean_st_ref_set(v___y_2667_, v___x_2694_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_r_2688_);
return v___x_2696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg___boxed(lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_2702_);
lean_dec(v___y_2702_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_2708_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___boxed(lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(lean_object* v_ref_2717_, lean_object* v_proof_2718_, lean_object* v_prio_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v___x_2725_; 
lean_inc(v_a_2723_);
lean_inc_ref(v_a_2722_);
lean_inc(v_a_2721_);
lean_inc_ref(v_a_2720_);
lean_inc_ref(v_proof_2718_);
v___x_2725_ = lean_infer_type(v_proof_2718_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; lean_object* v_a_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref(v___x_2725_);
v___x_2727_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v_a_2723_);
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref(v___x_2727_);
v___x_2729_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2729_, 0, v_a_2728_);
lean_ctor_set(v___x_2729_, 1, v_ref_2717_);
lean_ctor_set(v___x_2729_, 2, v_proof_2718_);
v___x_2730_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_2726_, v___x_2729_, v_prio_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
return v___x_2730_;
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_prio_2719_);
lean_dec_ref(v_proof_2718_);
lean_dec(v_ref_2717_);
v_a_2731_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2725_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2725_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx___boxed(lean_object* v_ref_2739_, lean_object* v_proof_2740_, lean_object* v_prio_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(v_ref_2739_, v_proof_2740_, v_prio_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
return v_res_2747_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2748_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0);
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
return v___x_2750_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
return v___x_2752_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
v___x_2754_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
lean_ctor_set(v___x_2754_, 2, v___x_2753_);
lean_ctor_set(v___x_2754_, 3, v___x_2753_);
lean_ctor_set(v___x_2754_, 4, v___x_2753_);
lean_ctor_set(v___x_2754_, 5, v___x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(lean_object* v_ext_2755_, lean_object* v_b_2756_, uint8_t v_kind_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_currNamespace_2762_; lean_object* v___x_2763_; lean_object* v_env_2764_; lean_object* v_nextMacroScope_2765_; lean_object* v_ngen_2766_; lean_object* v_auxDeclNGen_2767_; lean_object* v_traceState_2768_; lean_object* v_messages_2769_; lean_object* v_infoState_2770_; lean_object* v_snapshotTasks_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2798_; 
v_currNamespace_2762_ = lean_ctor_get(v___y_2759_, 6);
v___x_2763_ = lean_st_ref_take(v___y_2760_);
v_env_2764_ = lean_ctor_get(v___x_2763_, 0);
v_nextMacroScope_2765_ = lean_ctor_get(v___x_2763_, 1);
v_ngen_2766_ = lean_ctor_get(v___x_2763_, 2);
v_auxDeclNGen_2767_ = lean_ctor_get(v___x_2763_, 3);
v_traceState_2768_ = lean_ctor_get(v___x_2763_, 4);
v_messages_2769_ = lean_ctor_get(v___x_2763_, 6);
v_infoState_2770_ = lean_ctor_get(v___x_2763_, 7);
v_snapshotTasks_2771_ = lean_ctor_get(v___x_2763_, 8);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; 
v_unused_2799_ = lean_ctor_get(v___x_2763_, 5);
lean_dec(v_unused_2799_);
v___x_2773_ = v___x_2763_;
v_isShared_2774_ = v_isSharedCheck_2798_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_snapshotTasks_2771_);
lean_inc(v_infoState_2770_);
lean_inc(v_messages_2769_);
lean_inc(v_traceState_2768_);
lean_inc(v_auxDeclNGen_2767_);
lean_inc(v_ngen_2766_);
lean_inc(v_nextMacroScope_2765_);
lean_inc(v_env_2764_);
lean_dec(v___x_2763_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2798_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
lean_inc(v_currNamespace_2762_);
v___x_2775_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2764_, v_ext_2755_, v_b_2756_, v_kind_2757_, v_currNamespace_2762_);
v___x_2776_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 5, v___x_2776_);
lean_ctor_set(v___x_2773_, 0, v___x_2775_);
v___x_2778_ = v___x_2773_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_nextMacroScope_2765_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_ngen_2766_);
lean_ctor_set(v_reuseFailAlloc_2797_, 3, v_auxDeclNGen_2767_);
lean_ctor_set(v_reuseFailAlloc_2797_, 4, v_traceState_2768_);
lean_ctor_set(v_reuseFailAlloc_2797_, 5, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2797_, 6, v_messages_2769_);
lean_ctor_set(v_reuseFailAlloc_2797_, 7, v_infoState_2770_);
lean_ctor_set(v_reuseFailAlloc_2797_, 8, v_snapshotTasks_2771_);
v___x_2778_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v_mctx_2781_; lean_object* v_zetaDeltaFVarIds_2782_; lean_object* v_postponed_2783_; lean_object* v_diag_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2795_; 
v___x_2779_ = lean_st_ref_set(v___y_2760_, v___x_2778_);
v___x_2780_ = lean_st_ref_take(v___y_2758_);
v_mctx_2781_ = lean_ctor_get(v___x_2780_, 0);
v_zetaDeltaFVarIds_2782_ = lean_ctor_get(v___x_2780_, 2);
v_postponed_2783_ = lean_ctor_get(v___x_2780_, 3);
v_diag_2784_ = lean_ctor_get(v___x_2780_, 4);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; 
v_unused_2796_ = lean_ctor_get(v___x_2780_, 1);
lean_dec(v_unused_2796_);
v___x_2786_ = v___x_2780_;
v_isShared_2787_ = v_isSharedCheck_2795_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_diag_2784_);
lean_inc(v_postponed_2783_);
lean_inc(v_zetaDeltaFVarIds_2782_);
lean_inc(v_mctx_2781_);
lean_dec(v___x_2780_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2795_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2788_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 1, v___x_2788_);
v___x_2790_ = v___x_2786_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_mctx_2781_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v___x_2788_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_zetaDeltaFVarIds_2782_);
lean_ctor_set(v_reuseFailAlloc_2794_, 3, v_postponed_2783_);
lean_ctor_set(v_reuseFailAlloc_2794_, 4, v_diag_2784_);
v___x_2790_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_st_ref_set(v___y_2758_, v___x_2790_);
v___x_2792_ = lean_box(0);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___boxed(lean_object* v_ext_2800_, lean_object* v_b_2801_, lean_object* v_kind_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
uint8_t v_kind_boxed_2807_; lean_object* v_res_2808_; 
v_kind_boxed_2807_ = lean_unbox(v_kind_2802_);
v_res_2808_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2800_, v_b_2801_, v_kind_boxed_2807_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(lean_object* v_00_u03b1_2809_, lean_object* v_00_u03b2_2810_, lean_object* v_00_u03c3_2811_, lean_object* v_ext_2812_, lean_object* v_b_2813_, uint8_t v_kind_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2812_, v_b_2813_, v_kind_2814_, v___y_2816_, v___y_2817_, v___y_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_00_u03b2_2822_, lean_object* v_00_u03c3_2823_, lean_object* v_ext_2824_, lean_object* v_b_2825_, lean_object* v_kind_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
uint8_t v_kind_boxed_2832_; lean_object* v_res_2833_; 
v_kind_boxed_2832_ = lean_unbox(v_kind_2826_);
v_res_2833_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(v_00_u03b1_2821_, v_00_u03b2_2822_, v_00_u03c3_2823_, v_ext_2824_, v_b_2825_, v_kind_boxed_2832_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(lean_object* v_ext_2834_, lean_object* v_declName_2835_, lean_object* v_prio_2836_, uint8_t v_attrKind_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_2835_, v_prio_2836_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref(v___x_2843_);
v___x_2845_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2834_, v_a_2844_, v_attrKind_2837_, v_a_2839_, v_a_2840_, v_a_2841_);
return v___x_2845_;
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref(v_ext_2834_);
v_a_2846_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2843_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2843_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst___boxed(lean_object* v_ext_2854_, lean_object* v_declName_2855_, lean_object* v_prio_2856_, lean_object* v_attrKind_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_){
_start:
{
uint8_t v_attrKind_boxed_2863_; lean_object* v_res_2864_; 
v_attrKind_boxed_2863_ = lean_unbox(v_attrKind_2857_);
v_res_2864_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(v_ext_2854_, v_declName_2855_, v_prio_2856_, v_attrKind_boxed_2863_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(lean_object* v_ext_2865_, lean_object* v_fvar_2866_, lean_object* v_prio_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvar_2866_, v_prio_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; uint8_t v___x_2875_; lean_object* v___x_2876_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref(v___x_2873_);
v___x_2875_ = 1;
v___x_2876_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2865_, v_a_2874_, v___x_2875_, v_a_2869_, v_a_2870_, v_a_2871_);
return v___x_2876_;
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec_ref(v_ext_2865_);
v_a_2877_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2873_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2873_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal___boxed(lean_object* v_ext_2885_, lean_object* v_fvar_2886_, lean_object* v_prio_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(v_ext_2885_, v_fvar_2886_, v_prio_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(uint8_t v_x_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___y_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed(lean_object* v_x_2897_, lean_object* v___y_2898_){
_start:
{
uint8_t v_x_31__boxed_2899_; lean_object* v_res_2900_; 
v_x_31__boxed_2899_ = lean_unbox(v_x_2897_);
v_res_2900_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(v_x_31__boxed_2899_, v___y_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(lean_object* v___y_2901_){
_start:
{
lean_inc_ref(v___y_2901_);
return v___y_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed(lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(v___y_2902_);
lean_dec_ref(v___y_2902_);
return v_res_2903_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5(void){
_start:
{
lean_object* v___f_2910_; lean_object* v___f_2911_; lean_object* v___x_2912_; lean_object* v___f_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___f_2910_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1));
v___f_2911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2));
v___x_2912_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2);
v___f_2913_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0));
v___x_2914_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4));
v___x_2915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
lean_ctor_set(v___x_2915_, 1, v___f_2913_);
lean_ctor_set(v___x_2915_, 2, v___x_2912_);
lean_ctor_set(v___x_2915_, 3, v___f_2911_);
lean_ctor_set(v___x_2915_, 4, v___f_2910_);
return v___x_2915_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt(void){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt;
v___x_2919_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2____boxed(lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
return v_res_2921_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0));
v___x_2924_ = l_Lean_stringToMessageData(v___x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(lean_object* v_____r_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1);
v___x_2932_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2931_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed(lean_object* v_____r_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(v_____r_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
return v_res_2939_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2940_; double v___x_2941_; 
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_float_of_nat(v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(lean_object* v_cls_2945_, lean_object* v_msg_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_ref_2952_; lean_object* v___x_2953_; lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2998_; 
v_ref_2952_ = lean_ctor_get(v___y_2949_, 5);
v___x_2953_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_2998_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2998_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v_traceState_2959_; lean_object* v_env_2960_; lean_object* v_nextMacroScope_2961_; lean_object* v_ngen_2962_; lean_object* v_auxDeclNGen_2963_; lean_object* v_cache_2964_; lean_object* v_messages_2965_; lean_object* v_infoState_2966_; lean_object* v_snapshotTasks_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2997_; 
v___x_2958_ = lean_st_ref_take(v___y_2950_);
v_traceState_2959_ = lean_ctor_get(v___x_2958_, 4);
v_env_2960_ = lean_ctor_get(v___x_2958_, 0);
v_nextMacroScope_2961_ = lean_ctor_get(v___x_2958_, 1);
v_ngen_2962_ = lean_ctor_get(v___x_2958_, 2);
v_auxDeclNGen_2963_ = lean_ctor_get(v___x_2958_, 3);
v_cache_2964_ = lean_ctor_get(v___x_2958_, 5);
v_messages_2965_ = lean_ctor_get(v___x_2958_, 6);
v_infoState_2966_ = lean_ctor_get(v___x_2958_, 7);
v_snapshotTasks_2967_ = lean_ctor_get(v___x_2958_, 8);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2969_ = v___x_2958_;
v_isShared_2970_ = v_isSharedCheck_2997_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_snapshotTasks_2967_);
lean_inc(v_infoState_2966_);
lean_inc(v_messages_2965_);
lean_inc(v_cache_2964_);
lean_inc(v_traceState_2959_);
lean_inc(v_auxDeclNGen_2963_);
lean_inc(v_ngen_2962_);
lean_inc(v_nextMacroScope_2961_);
lean_inc(v_env_2960_);
lean_dec(v___x_2958_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2997_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
uint64_t v_tid_2971_; lean_object* v_traces_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2996_; 
v_tid_2971_ = lean_ctor_get_uint64(v_traceState_2959_, sizeof(void*)*1);
v_traces_2972_ = lean_ctor_get(v_traceState_2959_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_traceState_2959_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2974_ = v_traceState_2959_;
v_isShared_2975_ = v_isSharedCheck_2996_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_traces_2972_);
lean_dec(v_traceState_2959_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2996_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; double v___x_2977_; uint8_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2986_; 
v___x_2976_ = lean_box(0);
v___x_2977_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0);
v___x_2978_ = 0;
v___x_2979_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1));
v___x_2980_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2980_, 0, v_cls_2945_);
lean_ctor_set(v___x_2980_, 1, v___x_2976_);
lean_ctor_set(v___x_2980_, 2, v___x_2979_);
lean_ctor_set_float(v___x_2980_, sizeof(void*)*3, v___x_2977_);
lean_ctor_set_float(v___x_2980_, sizeof(void*)*3 + 8, v___x_2977_);
lean_ctor_set_uint8(v___x_2980_, sizeof(void*)*3 + 16, v___x_2978_);
v___x_2981_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2));
v___x_2982_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v_a_2954_);
lean_ctor_set(v___x_2982_, 2, v___x_2981_);
lean_inc(v_ref_2952_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v_ref_2952_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = l_Lean_PersistentArray_push___redArg(v_traces_2972_, v___x_2983_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2984_);
v___x_2986_ = v___x_2974_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2984_);
lean_ctor_set_uint64(v_reuseFailAlloc_2995_, sizeof(void*)*1, v_tid_2971_);
v___x_2986_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2988_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 4, v___x_2986_);
v___x_2988_ = v___x_2969_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_env_2960_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_nextMacroScope_2961_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_ngen_2962_);
lean_ctor_set(v_reuseFailAlloc_2994_, 3, v_auxDeclNGen_2963_);
lean_ctor_set(v_reuseFailAlloc_2994_, 4, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_2994_, 5, v_cache_2964_);
lean_ctor_set(v_reuseFailAlloc_2994_, 6, v_messages_2965_);
lean_ctor_set(v_reuseFailAlloc_2994_, 7, v_infoState_2966_);
lean_ctor_set(v_reuseFailAlloc_2994_, 8, v_snapshotTasks_2967_);
v___x_2988_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2989_ = lean_st_ref_set(v___y_2950_, v___x_2988_);
v___x_2990_ = lean_box(0);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v___x_2990_);
v___x_2992_ = v___x_2956_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___boxed(lean_object* v_cls_2999_, lean_object* v_msg_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v_cls_2999_, v_msg_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(lean_object* v_constName_3007_, uint8_t v_skipRealize_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v___x_3014_; lean_object* v_env_3015_; lean_object* v___x_3016_; 
v___x_3014_ = lean_st_ref_get(v___y_3012_);
v_env_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc_ref(v_env_3015_);
lean_dec(v___x_3014_);
lean_inc(v_constName_3007_);
v___x_3016_ = l_Lean_Environment_findAsync_x3f(v_env_3015_, v_constName_3007_, v_skipRealize_3008_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_3007_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
return v___x_3017_;
}
else
{
lean_object* v_val_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v_constName_3007_);
v_val_3018_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3016_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_val_3018_);
lean_dec(v___x_3016_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set_tag(v___x_3020_, 0);
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_val_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0___boxed(lean_object* v_constName_3026_, lean_object* v_skipRealize_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
uint8_t v_skipRealize_boxed_3033_; lean_object* v_res_3034_; 
v_skipRealize_boxed_3033_ = lean_unbox(v_skipRealize_3027_);
v_res_3034_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_constName_3026_, v_skipRealize_boxed_3033_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
return v_res_3034_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3041_; uint64_t v___x_3042_; 
v___x_3041_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0));
v___x_3042_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3041_);
return v___x_3042_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1);
v___x_3044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0));
v___x_3045_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set_uint64(v___x_3045_, sizeof(void*)*1, v___x_3043_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3046_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3);
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3049_ = lean_box(1);
v___x_3050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_3051_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set(v___x_3052_, 1, v___x_3050_);
lean_ctor_set(v___x_3052_, 2, v___x_3049_);
return v___x_3052_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3055_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3056_ = lean_unsigned_to_nat(0u);
v___x_3057_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
lean_ctor_set(v___x_3057_, 2, v___x_3056_);
lean_ctor_set(v___x_3057_, 3, v___x_3056_);
lean_ctor_set(v___x_3057_, 4, v___x_3055_);
lean_ctor_set(v___x_3057_, 5, v___x_3055_);
lean_ctor_set(v___x_3057_, 6, v___x_3055_);
lean_ctor_set(v___x_3057_, 7, v___x_3055_);
lean_ctor_set(v___x_3057_, 8, v___x_3055_);
lean_ctor_set(v___x_3057_, 9, v___x_3055_);
return v___x_3057_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3059_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
lean_ctor_set(v___x_3059_, 2, v___x_3058_);
lean_ctor_set(v___x_3059_, 3, v___x_3058_);
lean_ctor_set(v___x_3059_, 4, v___x_3058_);
lean_ctor_set(v___x_3059_, 5, v___x_3058_);
return v___x_3059_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
lean_ctor_set(v___x_3061_, 2, v___x_3060_);
lean_ctor_set(v___x_3061_, 3, v___x_3060_);
lean_ctor_set(v___x_3061_, 4, v___x_3060_);
return v___x_3061_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12));
v___x_3067_ = l_Lean_stringToMessageData(v___x_3066_);
return v___x_3067_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_3069_ = l_String_toRawSubstring_x27(v___x_3068_);
return v___x_3069_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17(void){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Array_mkArray0(lean_box(0));
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(lean_object* v___x_3076_, lean_object* v_ext_3077_, lean_object* v___f_3078_, lean_object* v___x_3079_, lean_object* v___x_3080_, lean_object* v___x_3081_, lean_object* v___x_3082_, lean_object* v_declName_3083_, lean_object* v_stx_3084_, uint8_t v_attrKind_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
uint8_t v___x_3089_; uint8_t v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3089_ = 0;
v___x_3090_ = 1;
v___x_3091_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2);
v___x_3092_ = lean_unsigned_to_nat(0u);
v___x_3093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_3094_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5);
v___x_3095_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6));
v___x_3096_ = lean_box(0);
lean_inc(v___x_3076_);
v___x_3097_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3097_, 0, v___x_3091_);
lean_ctor_set(v___x_3097_, 1, v___x_3076_);
lean_ctor_set(v___x_3097_, 2, v___x_3094_);
lean_ctor_set(v___x_3097_, 3, v___x_3095_);
lean_ctor_set(v___x_3097_, 4, v___x_3096_);
lean_ctor_set(v___x_3097_, 5, v___x_3092_);
lean_ctor_set(v___x_3097_, 6, v___x_3096_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*7, v___x_3089_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*7 + 1, v___x_3089_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*7 + 2, v___x_3089_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*7 + 3, v___x_3090_);
v___x_3098_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7);
v___x_3099_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8);
v___x_3100_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9);
v___x_3101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3098_);
lean_ctor_set(v___x_3101_, 1, v___x_3099_);
lean_ctor_set(v___x_3101_, 2, v___x_3076_);
lean_ctor_set(v___x_3101_, 3, v___x_3093_);
lean_ctor_set(v___x_3101_, 4, v___x_3100_);
v___x_3102_ = lean_st_mk_ref(v___x_3101_);
lean_inc(v_declName_3083_);
v___x_3103_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_declName_3083_, v___x_3089_, v___x_3097_, v___x_3102_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_dec_ref(v___x_3103_);
v___x_3104_ = lean_unsigned_to_nat(1u);
v___x_3105_ = l_Lean_Syntax_getArg(v_stx_3084_, v___x_3104_);
lean_inc(v___x_3105_);
v___x_3106_ = l_Lean_getAttrParamOptPrio(v___x_3105_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3202_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3202_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3202_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___y_3118_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; uint8_t v___y_3126_; lean_object* v___x_3139_; 
v___x_3111_ = lean_box(0);
lean_inc(v_declName_3083_);
v___x_3139_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(v_ext_3077_, v_declName_3083_, v_a_3107_, v_attrKind_3085_, v___x_3097_, v___x_3102_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_dec(v___x_3105_);
lean_dec_ref(v___x_3097_);
lean_dec(v_declName_3083_);
lean_dec_ref(v___x_3082_);
lean_dec_ref(v___x_3081_);
lean_dec_ref(v___x_3080_);
lean_dec_ref(v___x_3079_);
lean_dec_ref(v___f_3078_);
v___y_3118_ = v___x_3139_;
goto v___jp_3117_;
}
else
{
lean_object* v_a_3140_; uint8_t v___y_3142_; uint8_t v___x_3200_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
v___x_3200_ = l_Lean_Exception_isInterrupt(v_a_3140_);
if (v___x_3200_ == 0)
{
uint8_t v___x_3201_; 
v___x_3201_ = l_Lean_Exception_isRuntime(v_a_3140_);
v___y_3142_ = v___x_3201_;
goto v___jp_3141_;
}
else
{
lean_dec(v_a_3140_);
v___y_3142_ = v___x_3200_;
goto v___jp_3141_;
}
v___jp_3141_:
{
if (v___y_3142_ == 0)
{
lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3198_; 
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; 
v_unused_3199_ = lean_ctor_get(v___x_3139_, 0);
lean_dec(v_unused_3199_);
v___x_3144_ = v___x_3139_;
v_isShared_3145_ = v_isSharedCheck_3198_;
goto v_resetjp_3143_;
}
else
{
lean_dec(v___x_3139_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3198_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_3147_ = l_Lean_getBuiltinAttributeImpl(v___x_3146_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v_options_3149_; lean_object* v_ref_3150_; lean_object* v_quotContext_3151_; lean_object* v_currMacroScope_3152_; lean_object* v_inheritedTraceOptions_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v_add_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3180_; 
lean_del_object(v___x_3144_);
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref(v___x_3147_);
v_options_3149_ = lean_ctor_get(v___y_3086_, 2);
v_ref_3150_ = lean_ctor_get(v___y_3086_, 5);
v_quotContext_3151_ = lean_ctor_get(v___y_3086_, 10);
v_currMacroScope_3152_ = lean_ctor_get(v___y_3086_, 11);
v_inheritedTraceOptions_3153_ = lean_ctor_get(v___y_3086_, 13);
v___x_3154_ = l_Lean_SourceInfo_fromRef(v_ref_3150_, v___y_3142_);
v___x_3155_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14);
lean_inc(v_currMacroScope_3152_);
lean_inc(v_quotContext_3151_);
v___x_3156_ = l_Lean_addMacroScope(v_quotContext_3151_, v___x_3146_, v_currMacroScope_3152_);
v___x_3157_ = lean_box(0);
lean_inc(v___x_3154_);
v___x_3158_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3154_);
lean_ctor_set(v___x_3158_, 1, v___x_3155_);
lean_ctor_set(v___x_3158_, 2, v___x_3156_);
lean_ctor_set(v___x_3158_, 3, v___x_3157_);
v_add_3159_ = lean_ctor_get(v_a_3148_, 1);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_a_3148_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; lean_object* v_unused_3182_; 
v_unused_3181_ = lean_ctor_get(v_a_3148_, 2);
lean_dec(v_unused_3181_);
v_unused_3182_ = lean_ctor_get(v_a_3148_, 0);
lean_dec(v_unused_3182_);
v___x_3161_ = v_a_3148_;
v_isShared_3162_ = v_isSharedCheck_3180_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_add_3159_);
lean_dec(v_a_3148_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3180_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3163_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16));
v___x_3164_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17);
lean_inc(v___x_3154_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set_tag(v___x_3161_, 1);
lean_ctor_set(v___x_3161_, 2, v___x_3164_);
lean_ctor_set(v___x_3161_, 1, v___x_3163_);
lean_ctor_set(v___x_3161_, 0, v___x_3154_);
v___x_3166_ = v___x_3161_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3179_, 2, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3167_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18));
v___x_3168_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3169_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19));
v___x_3170_ = l_Lean_Name_mkStr4(v___x_3082_, v___x_3167_, v___x_3168_, v___x_3169_);
v___x_3171_ = l_Lean_Syntax_node2(v___x_3154_, v___x_3170_, v___x_3158_, v___x_3166_);
v___x_3172_ = lean_unsigned_to_nat(3u);
v___x_3173_ = l_Lean_Syntax_setArg(v___x_3171_, v___x_3172_, v___x_3105_);
v___x_3174_ = lean_box(v_attrKind_3085_);
lean_inc(v___y_3087_);
lean_inc_ref(v___y_3086_);
v___x_3175_ = lean_apply_6(v_add_3159_, v_declName_3083_, v___x_3173_, v___x_3174_, v___y_3086_, v___y_3087_, lean_box(0));
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_dec_ref(v___x_3175_);
lean_dec_ref(v___x_3097_);
lean_dec_ref(v___x_3081_);
lean_dec_ref(v___x_3080_);
lean_dec_ref(v___x_3079_);
lean_dec_ref(v___f_3078_);
goto v___jp_3112_;
}
else
{
lean_object* v_a_3176_; uint8_t v___x_3177_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_a_3176_);
v___x_3177_ = l_Lean_Exception_isInterrupt(v_a_3176_);
if (v___x_3177_ == 0)
{
uint8_t v___x_3178_; 
lean_inc(v_a_3176_);
v___x_3178_ = l_Lean_Exception_isRuntime(v_a_3176_);
v___y_3122_ = v___x_3175_;
v___y_3123_ = v_a_3176_;
v___y_3124_ = v_inheritedTraceOptions_3153_;
v___y_3125_ = v_options_3149_;
v___y_3126_ = v___x_3178_;
goto v___jp_3121_;
}
else
{
v___y_3122_ = v___x_3175_;
v___y_3123_ = v_a_3176_;
v___y_3124_ = v_inheritedTraceOptions_3153_;
v___y_3125_ = v_options_3149_;
v___y_3126_ = v___x_3177_;
goto v___jp_3121_;
}
}
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3197_; 
lean_del_object(v___x_3109_);
lean_dec(v___x_3105_);
lean_dec(v___x_3102_);
lean_dec_ref(v___x_3097_);
lean_dec(v_declName_3083_);
lean_dec_ref(v___x_3082_);
lean_dec_ref(v___x_3081_);
lean_dec_ref(v___x_3080_);
lean_dec_ref(v___x_3079_);
lean_dec_ref(v___f_3078_);
v_a_3183_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3185_ = v___x_3147_;
v_isShared_3186_ = v_isSharedCheck_3197_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3147_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3197_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_ref_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v_ref_3187_ = lean_ctor_get(v___y_3086_, 5);
v___x_3188_ = lean_io_error_to_string(v_a_3183_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set_tag(v___x_3144_, 3);
lean_ctor_set(v___x_3144_, 0, v___x_3188_);
v___x_3190_ = v___x_3144_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3194_; 
v___x_3191_ = l_Lean_MessageData_ofFormat(v___x_3190_);
lean_inc(v_ref_3187_);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v_ref_3187_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v___x_3192_);
v___x_3194_ = v___x_3185_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3105_);
lean_dec_ref(v___x_3097_);
lean_dec(v_declName_3083_);
lean_dec_ref(v___x_3082_);
lean_dec_ref(v___x_3081_);
lean_dec_ref(v___x_3080_);
lean_dec_ref(v___x_3079_);
lean_dec_ref(v___f_3078_);
v___y_3118_ = v___x_3139_;
goto v___jp_3117_;
}
}
}
v___jp_3112_:
{
lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3113_ = lean_st_ref_get(v___x_3102_);
lean_dec(v___x_3102_);
lean_dec(v___x_3113_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3111_);
v___x_3115_ = v___x_3109_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3111_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
v___jp_3117_:
{
if (lean_obj_tag(v___y_3118_) == 0)
{
lean_dec_ref(v___y_3118_);
goto v___jp_3112_;
}
else
{
lean_del_object(v___x_3109_);
lean_dec(v___x_3102_);
return v___y_3118_;
}
}
v___jp_3119_:
{
lean_object* v___x_3120_; 
lean_inc(v___y_3087_);
lean_inc_ref(v___y_3086_);
lean_inc(v___x_3102_);
v___x_3120_ = lean_apply_6(v___f_3078_, v___x_3111_, v___x_3097_, v___x_3102_, v___y_3086_, v___y_3087_, lean_box(0));
v___y_3118_ = v___x_3120_;
goto v___jp_3117_;
}
v___jp_3121_:
{
if (v___y_3126_ == 0)
{
uint8_t v_hasTrace_3127_; 
lean_dec_ref(v___y_3122_);
v_hasTrace_3127_ = lean_ctor_get_uint8(v___y_3125_, sizeof(void*)*1);
if (v_hasTrace_3127_ == 0)
{
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___x_3081_);
lean_dec_ref(v___x_3080_);
lean_dec_ref(v___x_3079_);
goto v___jp_3119_;
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v___x_3128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3129_ = l_Lean_Name_mkStr4(v___x_3079_, v___x_3080_, v___x_3081_, v___x_3128_);
v___x_3130_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11));
lean_inc(v___x_3129_);
v___x_3131_ = l_Lean_Name_append(v___x_3130_, v___x_3129_);
v___x_3132_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_3124_, v___y_3125_, v___x_3131_);
lean_dec(v___x_3131_);
if (v___x_3132_ == 0)
{
lean_dec(v___x_3129_);
lean_dec_ref(v___y_3123_);
goto v___jp_3119_;
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3133_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13);
v___x_3134_ = l_Lean_Exception_toMessageData(v___y_3123_);
v___x_3135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v___x_3129_, v___x_3135_, v___x_3097_, v___x_3102_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3138_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref(v___x_3136_);
lean_inc(v___y_3087_);
lean_inc_ref(v___y_3086_);
lean_inc(v___x_3102_);
v___x_3138_ = lean_apply_6(v___f_3078_, v_a_3137_, v___x_3097_, v___x_3102_, v___y_3086_, v___y_3087_, lean_box(0));
v___y_3118_ = v___x_3138_;
goto v___jp_3117_;
}
else
{
lean_dec_ref(v___x_3097_);
lean_dec_ref(v___f_3078_);
v___y_3118_ = v___x_3136_;
goto v___jp_3117_;
}
}
}
}
else
{
lean_dec_ref(v___y_3123_);
lean_del_object(v___x_3109_);
lean_dec(v___x_3102_);
lean_dec_ref(v___x_3097_);
lean_dec_ref(v___x_3081_);
lean_dec_ref(v___x_3080_);
lean_dec_ref(v___x_3079_);
lean_dec_ref(v___f_3078_);
return v___y_3122_;
}
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v___x_3105_);
lean_dec(v___x_3102_);
lean_dec_ref(v___x_3097_);
lean_dec(v_declName_3083_);
lean_dec_ref(v___x_3082_);
lean_dec_ref(v___x_3081_);
lean_dec_ref(v___x_3080_);
lean_dec_ref(v___x_3079_);
lean_dec_ref(v___f_3078_);
lean_dec_ref(v_ext_3077_);
v_a_3203_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3106_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3106_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
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
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v___x_3102_);
lean_dec_ref(v___x_3097_);
lean_dec(v_declName_3083_);
lean_dec_ref(v___x_3082_);
lean_dec_ref(v___x_3081_);
lean_dec_ref(v___x_3080_);
lean_dec_ref(v___x_3079_);
lean_dec_ref(v___f_3078_);
lean_dec_ref(v_ext_3077_);
v_a_3211_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3103_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3103_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed(lean_object* v___x_3219_, lean_object* v_ext_3220_, lean_object* v___f_3221_, lean_object* v___x_3222_, lean_object* v___x_3223_, lean_object* v___x_3224_, lean_object* v___x_3225_, lean_object* v_declName_3226_, lean_object* v_stx_3227_, lean_object* v_attrKind_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
uint8_t v_attrKind_boxed_3232_; lean_object* v_res_3233_; 
v_attrKind_boxed_3232_ = lean_unbox(v_attrKind_3228_);
v_res_3233_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(v___x_3219_, v_ext_3220_, v___f_3221_, v___x_3222_, v___x_3223_, v___x_3224_, v___x_3225_, v_declName_3226_, v_stx_3227_, v_attrKind_boxed_3232_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v_stx_3227_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(lean_object* v_msgData_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; lean_object* v_env_3239_; lean_object* v_options_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3238_ = lean_st_ref_get(v___y_3236_);
v_env_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc_ref(v_env_3239_);
lean_dec(v___x_3238_);
v_options_3240_ = lean_ctor_get(v___y_3235_, 2);
v___x_3241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_3242_ = lean_unsigned_to_nat(32u);
v___x_3243_ = lean_mk_empty_array_with_capacity(v___x_3242_);
lean_dec_ref(v___x_3243_);
v___x_3244_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
lean_inc_ref(v_options_3240_);
v___x_3245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3245_, 0, v_env_3239_);
lean_ctor_set(v___x_3245_, 1, v___x_3241_);
lean_ctor_set(v___x_3245_, 2, v___x_3244_);
lean_ctor_set(v___x_3245_, 3, v_options_3240_);
v___x_3246_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
lean_ctor_set(v___x_3246_, 1, v_msgData_3234_);
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2___boxed(lean_object* v_msgData_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msgData_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(lean_object* v_msg_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_ref_3257_; lean_object* v___x_3258_; lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3267_; 
v_ref_3257_ = lean_ctor_get(v___y_3254_, 5);
v___x_3258_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msg_3253_, v___y_3254_, v___y_3255_);
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3267_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3267_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v___x_3265_; 
lean_inc(v_ref_3257_);
v___x_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3263_, 0, v_ref_3257_);
lean_ctor_set(v___x_3263_, 1, v_a_3259_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set_tag(v___x_3261_, 1);
lean_ctor_set(v___x_3261_, 0, v___x_3263_);
v___x_3265_ = v___x_3261_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg___boxed(lean_object* v_msg_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v_msg_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3272_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0));
v___x_3275_ = l_Lean_stringToMessageData(v___x_3274_);
return v___x_3275_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2));
v___x_3278_ = l_Lean_stringToMessageData(v___x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(lean_object* v___x_3279_, lean_object* v_decl_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3284_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1);
v___x_3285_ = l_Lean_MessageData_ofName(v___x_3279_);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v___x_3288_, v___y_3281_, v___y_3282_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed(lean_object* v___x_3290_, lean_object* v_decl_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(v___x_3290_, v_decl_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v_decl_3291_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(lean_object* v_ext_3316_){
_start:
{
lean_object* v___f_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___f_3323_; lean_object* v___f_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___f_3317_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0));
v___x_3318_ = lean_box(1);
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___f_3323_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3323_, 0, v___x_3318_);
lean_closure_set(v___f_3323_, 1, v_ext_3316_);
lean_closure_set(v___f_3323_, 2, v___f_3317_);
lean_closure_set(v___f_3323_, 3, v___x_3320_);
lean_closure_set(v___f_3323_, 4, v___x_3321_);
lean_closure_set(v___f_3323_, 5, v___x_3322_);
lean_closure_set(v___f_3323_, 6, v___x_3319_);
v___f_3324_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5));
v___x_3325_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7));
v___x_3326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
lean_ctor_set(v___x_3326_, 1, v___f_3323_);
lean_ctor_set(v___x_3326_, 2, v___f_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(lean_object* v_00_u03b1_3327_, lean_object* v_msg_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v_msg_3328_, v___y_3329_, v___y_3330_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___boxed(lean_object* v_00_u03b1_3333_, lean_object* v_msg_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(v_00_u03b1_3333_, v_msg_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
return v_res_3338_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
v___x_3340_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(v___x_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3342_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_);
v___x_3343_ = l_Lean_registerBuiltinAttribute(v___x_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2____boxed(lean_object* v_a_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(lean_object* v_ext_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v___x_3349_; lean_object* v_ext_3350_; lean_object* v_toEnvExtension_3351_; lean_object* v_env_3352_; lean_object* v_asyncMode_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3349_ = lean_st_ref_get(v_a_3347_);
v_ext_3350_ = lean_ctor_get(v_ext_3346_, 1);
v_toEnvExtension_3351_ = lean_ctor_get(v_ext_3350_, 0);
v_env_3352_ = lean_ctor_get(v___x_3349_, 0);
lean_inc_ref(v_env_3352_);
lean_dec(v___x_3349_);
v_asyncMode_3353_ = lean_ctor_get(v_toEnvExtension_3351_, 2);
v___x_3354_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
v___x_3355_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3354_, v_ext_3346_, v_env_3352_, v_asyncMode_3353_);
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg___boxed(lean_object* v_ext_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_3357_, v_a_3358_);
lean_dec(v_a_3358_);
lean_dec_ref(v_ext_3357_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(lean_object* v_ext_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_3361_, v_a_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___boxed(lean_object* v_ext_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(v_ext_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec_ref(v_ext_3366_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(lean_object* v_a_3371_){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
v___x_3374_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v___x_3373_, v_a_3371_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg___boxed(lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3375_);
lean_dec(v_a_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3379_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___boxed(lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(v_a_3382_, v_a_3383_);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3382_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(lean_object* v_x_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = lean_box(0);
v___x_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object* v_x_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(v_x_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v_x_3392_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___f_3411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3415_ = 0;
v___x_3416_ = lean_box(2);
v___x_3417_ = l_Lean_registerTagAttribute(v___x_3412_, v___x_3413_, v___f_3411_, v___x_3414_, v___x_3415_, v___x_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
return v_res_3419_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(lean_object* v_env_3420_, lean_object* v_ty_3421_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Lean_Expr_getAppFn(v_ty_3421_);
if (lean_obj_tag(v___x_3422_) == 4)
{
lean_object* v_declName_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v_declName_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_declName_3423_);
lean_dec_ref(v___x_3422_);
v___x_3424_ = l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr;
v___x_3425_ = l_Lean_TagAttribute_hasTag(v___x_3424_, v_env_3420_, v_declName_3423_);
return v___x_3425_;
}
else
{
uint8_t v___x_3426_; 
lean_dec_ref(v___x_3422_);
lean_dec_ref(v_env_3420_);
v___x_3426_ = 0;
return v___x_3426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType___boxed(lean_object* v_env_3427_, lean_object* v_ty_3428_){
_start:
{
uint8_t v_res_3429_; lean_object* v_r_3430_; 
v_res_3429_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v_env_3427_, v_ty_3428_);
lean_dec_ref(v_ty_3428_);
v_r_3430_ = lean_box(v_res_3429_);
return v_r_3430_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt);
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default = _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default);
l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem = _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem);
l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default = _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default);
l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems = _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems);
l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig = _init_l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig);
l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt = _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt);
res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Do_SpecAttr_specAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_specAttr);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
