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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value;
static const lean_array_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(lean_object*, lean_object*);
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
lean_dec_ref_known(v_t_134_, 3);
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
lean_dec_ref_known(v_x_182_, 1);
v_declName_185_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_declName_185_);
lean_dec_ref_known(v_x_183_, 1);
v___x_186_ = lean_name_eq(v_declName_184_, v_declName_185_);
lean_dec(v_declName_185_);
lean_dec(v_declName_184_);
return v___x_186_;
}
else
{
uint8_t v___x_187_; 
lean_dec_ref_known(v_x_182_, 1);
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
lean_dec_ref_known(v_x_182_, 1);
v_fvarId_189_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_fvarId_189_);
lean_dec_ref_known(v_x_183_, 1);
v___x_190_ = l_Lean_instBEqFVarId_beq(v_fvarId_188_, v_fvarId_189_);
lean_dec(v_fvarId_189_);
lean_dec(v_fvarId_188_);
return v___x_190_;
}
else
{
uint8_t v___x_191_; 
lean_dec_ref_known(v_x_182_, 1);
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
lean_dec_ref_known(v_x_182_, 3);
v_id_195_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_id_195_);
v_ref_196_ = lean_ctor_get(v_x_183_, 1);
lean_inc(v_ref_196_);
v_proof_197_ = lean_ctor_get(v_x_183_, 2);
lean_inc_ref(v_proof_197_);
lean_dec_ref_known(v_x_183_, 3);
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
lean_dec_ref_known(v_x_182_, 3);
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
lean_dec_ref_known(v___x_296_, 14);
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
lean_dec_ref_known(v_x_529_, 1);
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
lean_dec_ref_known(v_x_529_, 3);
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
lean_dec_ref_known(v_proof_740_, 1);
v___x_803_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_802_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
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
lean_dec_ref_known(v_proof_740_, 1);
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
lean_dec_ref_known(v_proof_740_, 3);
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
lean_dec_ref_known(v___x_752_, 1);
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
lean_dec_ref_known(v_x_835_, 1);
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
lean_dec_ref_known(v_x_835_, 1);
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
lean_dec_ref_known(v_x_835_, 3);
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
lean_dec_ref_known(v___x_1235_, 2);
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
lean_dec_ref_known(v___x_1361_, 1);
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
lean_dec_ref_known(v_x_1507_, 1);
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
lean_dec_ref_known(v___x_1516_, 2);
v___x_1518_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1509_, v_key_1517_);
return v___x_1518_;
}
case 1:
{
lean_object* v_node_1519_; size_t v___x_1520_; 
v_node_1519_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_node_1519_);
lean_dec_ref_known(v___x_1516_, 1);
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
lean_dec_ref_known(v_x_1507_, 2);
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
lean_dec_ref_known(v___x_1884_, 1);
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
lean_dec_ref_known(v___x_1900_, 1);
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
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1850_, v_value_1934_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
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
lean_dec_ref_known(v___x_1864_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(lean_object* v___x_2053_, lean_object* v___x_2054_, lean_object* v_fst_2055_, lean_object* v___x_2056_, lean_object* v_expr_2057_, lean_object* v_____r_2058_, lean_object* v_lastSuccess_2059_, lean_object* v_boundAssignments_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2066_ = lean_unsigned_to_nat(2u);
v___x_2067_ = lean_nat_sub(v___x_2053_, v___x_2066_);
v___x_2068_ = lean_nat_sub(v___x_2067_, v___x_2054_);
lean_dec(v___x_2067_);
v___x_2069_ = l_Lean_Expr_getRevArg_x21(v_fst_2055_, v___x_2068_);
v___x_2070_ = l_Lean_Meta_whnfR(v___x_2069_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2083_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2083_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2083_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_lastSuccess_2059_);
lean_ctor_set(v___x_2075_, 1, v_boundAssignments_2060_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2056_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v_expr_2057_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_a_2071_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2079_);
v___x_2081_ = v___x_2073_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v_boundAssignments_2060_);
lean_dec(v_lastSuccess_2059_);
lean_dec_ref(v_expr_2057_);
lean_dec(v___x_2056_);
v_a_2084_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2070_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2070_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0___boxed(lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v_fst_2094_, lean_object* v___x_2095_, lean_object* v_expr_2096_, lean_object* v_____r_2097_, lean_object* v_lastSuccess_2098_, lean_object* v_boundAssignments_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_2092_, v___x_2093_, v_fst_2094_, v___x_2095_, v_expr_2096_, v_____r_2097_, v_lastSuccess_2098_, v_boundAssignments_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v_fst_2094_);
lean_dec(v___x_2093_);
lean_dec(v___x_2092_);
return v_res_2105_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2113_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_unsigned_to_nat(0u);
v___x_2117_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2116_);
return v___x_2118_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = lean_unsigned_to_nat(32u);
v___x_2120_ = lean_mk_empty_array_with_capacity(v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8(void){
_start:
{
size_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2122_ = ((size_t)5ULL);
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = lean_unsigned_to_nat(32u);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2124_);
v___x_2126_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7);
v___x_2127_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2125_);
lean_ctor_set(v___x_2127_, 2, v___x_2123_);
lean_ctor_set(v___x_2127_, 3, v___x_2123_);
lean_ctor_set_usize(v___x_2127_, 4, v___x_2122_);
return v___x_2127_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8);
v___x_2129_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5);
v___x_2130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
lean_ctor_set(v___x_2130_, 2, v___x_2129_);
lean_ctor_set(v___x_2130_, 3, v___x_2128_);
return v___x_2130_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9);
v___x_2132_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v___x_2131_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(lean_object* v_a_2134_, lean_object* v_xs_2135_, lean_object* v_a_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___y_2143_; lean_object* v_snd_2163_; lean_object* v_snd_2164_; lean_object* v_snd_2165_; lean_object* v_fst_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2259_; 
v_snd_2163_ = lean_ctor_get(v_a_2136_, 1);
lean_inc(v_snd_2163_);
v_snd_2164_ = lean_ctor_get(v_snd_2163_, 1);
lean_inc(v_snd_2164_);
v_snd_2165_ = lean_ctor_get(v_snd_2164_, 1);
lean_inc(v_snd_2165_);
v_fst_2166_ = lean_ctor_get(v_a_2136_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_a_2136_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; 
v_unused_2260_ = lean_ctor_get(v_a_2136_, 1);
lean_dec(v_unused_2260_);
v___x_2168_ = v_a_2136_;
v_isShared_2169_ = v_isSharedCheck_2259_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_fst_2166_);
lean_dec(v_a_2136_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2259_;
goto v_resetjp_2167_;
}
v___jp_2142_:
{
if (lean_obj_tag(v___y_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2154_; 
v_a_2144_ = lean_ctor_get(v___y_2143_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___y_2143_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2146_ = v___y_2143_;
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___y_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
if (lean_obj_tag(v_a_2144_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2150_; 
lean_dec_ref(v_a_2134_);
v_a_2148_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v_a_2144_, 1);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v_a_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
else
{
lean_object* v_a_2152_; 
lean_del_object(v___x_2146_);
v_a_2152_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v_a_2144_, 1);
v_a_2136_ = v_a_2152_;
goto _start;
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v_a_2134_);
v_a_2155_ = lean_ctor_get(v___y_2143_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___y_2143_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___y_2143_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___y_2143_);
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
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
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
}
v_resetjp_2167_:
{
lean_object* v_fst_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2257_; 
v_fst_2170_ = lean_ctor_get(v_snd_2163_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_snd_2163_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; 
v_unused_2258_ = lean_ctor_get(v_snd_2163_, 1);
lean_dec(v_unused_2258_);
v___x_2172_ = v_snd_2163_;
v_isShared_2173_ = v_isSharedCheck_2257_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_fst_2170_);
lean_dec(v_snd_2163_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2257_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_fst_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2255_; 
v_fst_2174_ = lean_ctor_get(v_snd_2164_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_snd_2164_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v_snd_2164_, 1);
lean_dec(v_unused_2256_);
v___x_2176_ = v_snd_2164_;
v_isShared_2177_ = v_isSharedCheck_2255_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_fst_2174_);
lean_dec(v_snd_2164_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2255_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2254_; 
v_fst_2178_ = lean_ctor_get(v_snd_2165_, 0);
v_snd_2179_ = lean_ctor_get(v_snd_2165_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_snd_2165_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2181_ = v_snd_2165_;
v_isShared_2182_ = v_isSharedCheck_2254_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snd_2179_);
lean_inc(v_fst_2178_);
lean_dec(v_snd_2165_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2254_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2183_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2));
v___x_2184_ = lean_unsigned_to_nat(3u);
v___x_2185_ = l_Lean_Expr_isAppOfArity(v_fst_2166_, v___x_2183_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2187_; 
lean_dec_ref(v_a_2134_);
if (v_isShared_2182_ == 0)
{
v___x_2187_ = v___x_2181_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_fst_2178_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_snd_2179_);
v___x_2187_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v___x_2187_);
v___x_2189_ = v___x_2176_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_fst_2174_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v___x_2189_);
v___x_2191_ = v___x_2172_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_fst_2170_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2193_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v___x_2191_);
v___x_2193_ = v___x_2168_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_fst_2166_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
}
}
}
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_del_object(v___x_2181_);
lean_del_object(v___x_2176_);
lean_del_object(v___x_2172_);
lean_del_object(v___x_2168_);
v___x_2199_ = lean_unsigned_to_nat(1u);
v___x_2200_ = l_Lean_Expr_getAppNumArgs(v_fst_2166_);
v___x_2201_ = lean_nat_sub(v___x_2200_, v___x_2199_);
v___x_2202_ = lean_nat_sub(v___x_2201_, v___x_2199_);
lean_dec(v___x_2201_);
v___x_2203_ = l_Lean_Expr_getRevArg_x21(v_fst_2166_, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
v___x_2205_ = 0;
v___x_2206_ = lean_box(0);
v___x_2207_ = l_Lean_Meta_mkFreshExprMVar(v___x_2204_, v___x_2205_, v___x_2206_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2209_ = lean_mk_empty_array_with_capacity(v___x_2199_);
v___x_2210_ = lean_array_push(v___x_2209_, v_a_2208_);
v___x_2211_ = l_Lean_Expr_beta(v_fst_2170_, v___x_2210_);
v___x_2212_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3));
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10);
lean_inc_ref(v_a_2134_);
v___x_2215_ = l_Lean_Meta_simp(v___x_2211_, v_a_2134_, v___x_2212_, v___x_2213_, v___x_2214_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v_fst_2217_; lean_object* v_expr_2218_; lean_object* v___x_2219_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v_fst_2217_ = lean_ctor_get(v_a_2216_, 0);
lean_inc(v_fst_2217_);
lean_dec(v_a_2216_);
v_expr_2218_ = lean_ctor_get(v_fst_2217_, 0);
lean_inc_ref(v_expr_2218_);
lean_dec(v_fst_2217_);
v___x_2219_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2135_, v_expr_2218_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2221_; uint8_t v___x_2225_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = lean_nat_add(v_fst_2174_, v___x_2199_);
lean_dec(v_fst_2174_);
v___x_2225_ = lean_nat_dec_lt(v_a_2220_, v_snd_2179_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = l_Lean_Expr_getAppFn_x27(v_expr_2218_);
v___x_2227_ = l_Lean_Expr_isMVar(v___x_2226_);
lean_dec_ref(v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec(v_a_2220_);
v___x_2228_ = lean_box(0);
v___x_2229_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_2200_, v___x_2199_, v_fst_2166_, v___x_2221_, v_expr_2218_, v___x_2228_, v_fst_2178_, v_snd_2179_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v_fst_2166_);
lean_dec(v___x_2200_);
v___y_2143_ = v___x_2229_;
goto v___jp_2142_;
}
else
{
lean_dec(v_snd_2179_);
lean_dec(v_fst_2178_);
goto v___jp_2222_;
}
}
else
{
lean_dec(v_snd_2179_);
lean_dec(v_fst_2178_);
goto v___jp_2222_;
}
v___jp_2222_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_box(0);
lean_inc(v___x_2221_);
v___x_2224_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_2200_, v___x_2199_, v_fst_2166_, v___x_2221_, v_expr_2218_, v___x_2223_, v___x_2221_, v_a_2220_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v_fst_2166_);
lean_dec(v___x_2200_);
v___y_2143_ = v___x_2224_;
goto v___jp_2142_;
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v_expr_2218_);
lean_dec(v___x_2200_);
lean_dec(v_snd_2179_);
lean_dec(v_fst_2178_);
lean_dec(v_fst_2174_);
lean_dec(v_fst_2166_);
lean_dec_ref(v_a_2134_);
v_a_2230_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2219_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2219_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v___x_2200_);
lean_dec(v_snd_2179_);
lean_dec(v_fst_2178_);
lean_dec(v_fst_2174_);
lean_dec(v_fst_2166_);
lean_dec_ref(v_a_2134_);
v_a_2238_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2215_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2215_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v___x_2200_);
lean_dec(v_snd_2179_);
lean_dec(v_fst_2178_);
lean_dec(v_fst_2174_);
lean_dec(v_fst_2170_);
lean_dec(v_fst_2166_);
lean_dec_ref(v_a_2134_);
v_a_2246_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2207_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2207_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___boxed(lean_object* v_a_2261_, lean_object* v_xs_2262_, lean_object* v_a_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_2261_, v_xs_2262_, v_a_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_xs_2262_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(lean_object* v___x_2270_, uint8_t v___x_2271_, lean_object* v_00_u03c3s_2272_, lean_object* v_xs_2273_, lean_object* v_e_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
if (v___x_2271_ == 0)
{
lean_object* v_config_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2354_; 
v_config_2280_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2282_ = v___x_2270_;
v_isShared_2283_ = v_isSharedCheck_2354_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_config_2280_);
lean_dec(v___x_2270_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2354_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
uint8_t v_trackZetaDelta_2284_; lean_object* v_zetaDeltaSet_2285_; lean_object* v_lctx_2286_; lean_object* v_localInstances_2287_; lean_object* v_defEqCtx_x3f_2288_; lean_object* v_synthPendingDepth_2289_; lean_object* v_canUnfold_x3f_2290_; uint8_t v_univApprox_2291_; uint8_t v_inTypeClassResolution_2292_; uint8_t v_cacheInferType_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2352_; 
v_trackZetaDelta_2284_ = lean_ctor_get_uint8(v___y_2275_, sizeof(void*)*7);
v_zetaDeltaSet_2285_ = lean_ctor_get(v___y_2275_, 1);
v_lctx_2286_ = lean_ctor_get(v___y_2275_, 2);
v_localInstances_2287_ = lean_ctor_get(v___y_2275_, 3);
v_defEqCtx_x3f_2288_ = lean_ctor_get(v___y_2275_, 4);
v_synthPendingDepth_2289_ = lean_ctor_get(v___y_2275_, 5);
v_canUnfold_x3f_2290_ = lean_ctor_get(v___y_2275_, 6);
v_univApprox_2291_ = lean_ctor_get_uint8(v___y_2275_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2292_ = lean_ctor_get_uint8(v___y_2275_, sizeof(void*)*7 + 2);
v_cacheInferType_2293_ = lean_ctor_get_uint8(v___y_2275_, sizeof(void*)*7 + 3);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___y_2275_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; 
v_unused_2353_ = lean_ctor_get(v___y_2275_, 0);
lean_dec(v_unused_2353_);
v___x_2295_ = v___y_2275_;
v_isShared_2296_ = v_isSharedCheck_2352_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_canUnfold_x3f_2290_);
lean_inc(v_synthPendingDepth_2289_);
lean_inc(v_defEqCtx_x3f_2288_);
lean_inc(v_localInstances_2287_);
lean_inc(v_lctx_2286_);
lean_inc(v_zetaDeltaSet_2285_);
lean_dec(v___y_2275_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2352_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
uint64_t v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2280_);
if (v_isShared_2283_ == 0)
{
v___x_2299_ = v___x_2282_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_config_2280_);
v___x_2299_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2301_; 
lean_ctor_set_uint64(v___x_2299_, sizeof(void*)*1, v___x_2297_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2299_);
v___x_2301_ = v___x_2295_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_zetaDeltaSet_2285_);
lean_ctor_set(v_reuseFailAlloc_2350_, 2, v_lctx_2286_);
lean_ctor_set(v_reuseFailAlloc_2350_, 3, v_localInstances_2287_);
lean_ctor_set(v_reuseFailAlloc_2350_, 4, v_defEqCtx_x3f_2288_);
lean_ctor_set(v_reuseFailAlloc_2350_, 5, v_synthPendingDepth_2289_);
lean_ctor_set(v_reuseFailAlloc_2350_, 6, v_canUnfold_x3f_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2350_, sizeof(void*)*7, v_trackZetaDelta_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2350_, sizeof(void*)*7 + 1, v_univApprox_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2350_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2350_, sizeof(void*)*7 + 3, v_cacheInferType_2293_);
v___x_2301_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v___x_2301_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_Meta_whnfR(v_00_u03c3s_2272_, v___x_2301_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2306_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2306_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2273_, v_e_2274_, v___x_2301_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v_a_2307_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v_e_2274_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v_a_2305_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_2303_, v_xs_2273_, v___x_2312_, v___x_2301_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec_ref(v___x_2301_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2325_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2325_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2325_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v_snd_2318_; lean_object* v_snd_2319_; lean_object* v_snd_2320_; lean_object* v_fst_2321_; lean_object* v___x_2323_; 
v_snd_2318_ = lean_ctor_get(v_a_2314_, 1);
lean_inc(v_snd_2318_);
lean_dec(v_a_2314_);
v_snd_2319_ = lean_ctor_get(v_snd_2318_, 1);
lean_inc(v_snd_2319_);
lean_dec(v_snd_2318_);
v_snd_2320_ = lean_ctor_get(v_snd_2319_, 1);
lean_inc(v_snd_2320_);
lean_dec(v_snd_2319_);
v_fst_2321_ = lean_ctor_get(v_snd_2320_, 0);
lean_inc(v_fst_2321_);
lean_dec(v_snd_2320_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v_fst_2321_);
v___x_2323_ = v___x_2316_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_fst_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2313_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2313_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
else
{
lean_dec(v_a_2305_);
lean_dec(v_a_2303_);
lean_dec_ref(v___x_2301_);
lean_dec_ref(v_e_2274_);
return v___x_2306_;
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2303_);
lean_dec_ref(v___x_2301_);
lean_dec_ref(v_e_2274_);
v_a_2334_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2304_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2304_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref(v___x_2301_);
lean_dec_ref(v_e_2274_);
lean_dec_ref(v_00_u03c3s_2272_);
v_a_2342_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2302_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2302_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
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
lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec_ref(v___y_2275_);
lean_dec_ref(v_e_2274_);
lean_dec_ref(v_00_u03c3s_2272_);
lean_dec_ref(v___x_2270_);
v___x_2355_ = lean_unsigned_to_nat(0u);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed(lean_object* v___x_2357_, lean_object* v___x_2358_, lean_object* v_00_u03c3s_2359_, lean_object* v_xs_2360_, lean_object* v_e_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
uint8_t v___x_5010__boxed_2367_; lean_object* v_res_2368_; 
v___x_5010__boxed_2367_ = lean_unbox(v___x_2358_);
v_res_2368_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(v___x_2357_, v___x_5010__boxed_2367_, v_00_u03c3s_2359_, v_xs_2360_, v_e_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v_xs_2360_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(lean_object* v_xs_2369_, lean_object* v_00_u03c3s_2370_, lean_object* v_e_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___f_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; 
v___x_2377_ = l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig;
v___x_2378_ = lean_array_get_size(v_xs_2369_);
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = lean_nat_dec_eq(v___x_2378_, v___x_2379_);
v___x_2381_ = lean_box(v___x_2380_);
v___f_2382_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2382_, 0, v___x_2377_);
lean_closure_set(v___f_2382_, 1, v___x_2381_);
lean_closure_set(v___f_2382_, 2, v_00_u03c3s_2370_);
lean_closure_set(v___f_2382_, 3, v_xs_2369_);
lean_closure_set(v___f_2382_, 4, v_e_2371_);
v___x_2383_ = 0;
v___x_2384_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_2382_, v___x_2383_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___boxed(lean_object* v_xs_2385_, lean_object* v_00_u03c3s_2386_, lean_object* v_e_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_xs_2385_, v_00_u03c3s_2386_, v_e_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(lean_object* v_a_2394_, lean_object* v_xs_2395_, lean_object* v_inst_2396_, lean_object* v_a_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_2394_, v_xs_2395_, v_a_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___boxed(lean_object* v_a_2404_, lean_object* v_xs_2405_, lean_object* v_inst_2406_, lean_object* v_a_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(v_a_2404_, v_xs_2405_, v_inst_2406_, v_a_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec_ref(v_xs_2405_);
return v_res_2413_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0));
v___x_2416_ = l_Lean_stringToMessageData(v___x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(lean_object* v_a_2430_, lean_object* v___x_2431_, uint8_t v___x_2432_, lean_object* v___x_2433_, lean_object* v_proof_2434_, lean_object* v_prio_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; lean_object* v_config_2442_; uint8_t v_trackZetaDelta_2443_; lean_object* v_zetaDeltaSet_2444_; lean_object* v_lctx_2445_; lean_object* v_localInstances_2446_; lean_object* v_defEqCtx_x3f_2447_; lean_object* v_synthPendingDepth_2448_; lean_object* v_canUnfold_x3f_2449_; uint8_t v_univApprox_2450_; uint8_t v_inTypeClassResolution_2451_; uint8_t v_cacheInferType_2452_; uint64_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2441_ = l_Lean_Meta_simpGlobalConfig;
v_config_2442_ = lean_ctor_get(v___x_2441_, 0);
v_trackZetaDelta_2443_ = lean_ctor_get_uint8(v___y_2436_, sizeof(void*)*7);
v_zetaDeltaSet_2444_ = lean_ctor_get(v___y_2436_, 1);
v_lctx_2445_ = lean_ctor_get(v___y_2436_, 2);
v_localInstances_2446_ = lean_ctor_get(v___y_2436_, 3);
v_defEqCtx_x3f_2447_ = lean_ctor_get(v___y_2436_, 4);
v_synthPendingDepth_2448_ = lean_ctor_get(v___y_2436_, 5);
v_canUnfold_x3f_2449_ = lean_ctor_get(v___y_2436_, 6);
v_univApprox_2450_ = lean_ctor_get_uint8(v___y_2436_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2451_ = lean_ctor_get_uint8(v___y_2436_, sizeof(void*)*7 + 2);
v_cacheInferType_2452_ = lean_ctor_get_uint8(v___y_2436_, sizeof(void*)*7 + 3);
v___x_2453_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2442_);
lean_inc_ref(v_config_2442_);
v___x_2454_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2454_, 0, v_config_2442_);
lean_ctor_set_uint64(v___x_2454_, sizeof(void*)*1, v___x_2453_);
lean_inc(v_canUnfold_x3f_2449_);
lean_inc(v_synthPendingDepth_2448_);
lean_inc(v_defEqCtx_x3f_2447_);
lean_inc_ref(v_localInstances_2446_);
lean_inc_ref(v_lctx_2445_);
lean_inc(v_zetaDeltaSet_2444_);
v___x_2455_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
lean_ctor_set(v___x_2455_, 1, v_zetaDeltaSet_2444_);
lean_ctor_set(v___x_2455_, 2, v_lctx_2445_);
lean_ctor_set(v___x_2455_, 3, v_localInstances_2446_);
lean_ctor_set(v___x_2455_, 4, v_defEqCtx_x3f_2447_);
lean_ctor_set(v___x_2455_, 5, v_synthPendingDepth_2448_);
lean_ctor_set(v___x_2455_, 6, v_canUnfold_x3f_2449_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*7, v_trackZetaDelta_2443_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*7 + 1, v_univApprox_2450_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2451_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*7 + 3, v_cacheInferType_2452_);
v___x_2456_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2430_, v___x_2431_, v___x_2432_, v___x_2455_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec_ref_known(v___x_2455_, 7);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v_snd_2458_; lean_object* v_fst_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2560_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v_snd_2458_ = lean_ctor_get(v_a_2457_, 1);
v_fst_2459_ = lean_ctor_get(v_a_2457_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_a_2457_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2461_ = v_a_2457_;
v_isShared_2462_ = v_isSharedCheck_2560_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_snd_2458_);
lean_inc(v_fst_2459_);
lean_dec(v_a_2457_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2560_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v_snd_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2558_; 
v_snd_2463_ = lean_ctor_get(v_snd_2458_, 1);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_snd_2458_);
if (v_isSharedCheck_2558_ == 0)
{
lean_object* v_unused_2559_; 
v_unused_2559_ = lean_ctor_get(v_snd_2458_, 0);
lean_dec(v_unused_2559_);
v___x_2465_ = v_snd_2458_;
v_isShared_2466_ = v_isSharedCheck_2558_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_snd_2463_);
lean_dec(v_snd_2458_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2558_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_Meta_whnfR(v_snd_2463_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_n(v_a_2468_, 2);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2480_ = l_Lean_Expr_cleanupAnnotations(v_a_2468_);
v___x_2481_ = l_Lean_Expr_isApp(v___x_2480_);
if (v___x_2481_ == 0)
{
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2461_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v___y_2470_ = v___y_2436_;
v___y_2471_ = v___y_2437_;
v___y_2472_ = v___y_2438_;
v___y_2473_ = v___y_2439_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2480_);
v___x_2483_ = l_Lean_Expr_isApp(v___x_2482_);
if (v___x_2483_ == 0)
{
lean_dec_ref(v___x_2482_);
lean_del_object(v___x_2461_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v___y_2470_ = v___y_2436_;
v___y_2471_ = v___y_2437_;
v___y_2472_ = v___y_2438_;
v___y_2473_ = v___y_2439_;
goto v___jp_2469_;
}
else
{
lean_object* v_arg_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_arg_2484_ = lean_ctor_get(v___x_2482_, 1);
lean_inc_ref(v_arg_2484_);
v___x_2485_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2482_);
v___x_2486_ = l_Lean_Expr_isApp(v___x_2485_);
if (v___x_2486_ == 0)
{
lean_dec_ref(v___x_2485_);
lean_dec_ref(v_arg_2484_);
lean_del_object(v___x_2461_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v___y_2470_ = v___y_2436_;
v___y_2471_ = v___y_2437_;
v___y_2472_ = v___y_2438_;
v___y_2473_ = v___y_2439_;
goto v___jp_2469_;
}
else
{
lean_object* v_arg_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v_arg_2487_ = lean_ctor_get(v___x_2485_, 1);
lean_inc_ref(v_arg_2487_);
v___x_2488_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2485_);
v___x_2489_ = l_Lean_Expr_isApp(v___x_2488_);
if (v___x_2489_ == 0)
{
lean_dec_ref(v___x_2488_);
lean_dec_ref(v_arg_2487_);
lean_dec_ref(v_arg_2484_);
lean_del_object(v___x_2461_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v___y_2470_ = v___y_2436_;
v___y_2471_ = v___y_2437_;
v___y_2472_ = v___y_2438_;
v___y_2473_ = v___y_2439_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2490_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2488_);
v___x_2491_ = l_Lean_Expr_isApp(v___x_2490_);
if (v___x_2491_ == 0)
{
lean_dec_ref(v___x_2490_);
lean_dec_ref(v_arg_2487_);
lean_dec_ref(v_arg_2484_);
lean_del_object(v___x_2461_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v___y_2470_ = v___y_2436_;
v___y_2471_ = v___y_2437_;
v___y_2472_ = v___y_2438_;
v___y_2473_ = v___y_2439_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2492_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2490_);
v___x_2493_ = l_Lean_Expr_isApp(v___x_2492_);
if (v___x_2493_ == 0)
{
lean_dec_ref(v___x_2492_);
lean_dec_ref(v_arg_2487_);
lean_dec_ref(v_arg_2484_);
lean_del_object(v___x_2461_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v___y_2470_ = v___y_2436_;
v___y_2471_ = v___y_2437_;
v___y_2472_ = v___y_2438_;
v___y_2473_ = v___y_2439_;
goto v___jp_2469_;
}
else
{
lean_object* v_arg_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v_arg_2494_ = lean_ctor_get(v___x_2492_, 1);
lean_inc_ref(v_arg_2494_);
v___x_2495_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2492_);
v___x_2496_ = l_Lean_Expr_isApp(v___x_2495_);
if (v___x_2496_ == 0)
{
lean_dec_ref(v___x_2495_);
lean_dec_ref(v_arg_2494_);
lean_dec_ref(v_arg_2487_);
lean_dec_ref(v_arg_2484_);
lean_del_object(v___x_2461_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v___y_2470_ = v___y_2436_;
v___y_2471_ = v___y_2437_;
v___y_2472_ = v___y_2438_;
v___y_2473_ = v___y_2439_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2497_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2495_);
v___x_2498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4));
v___x_2499_ = l_Lean_Expr_isConstOf(v___x_2497_, v___x_2498_);
if (v___x_2499_ == 0)
{
lean_dec_ref(v___x_2497_);
lean_dec_ref(v_arg_2494_);
lean_dec_ref(v_arg_2487_);
lean_dec_ref(v_arg_2484_);
lean_del_object(v___x_2461_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v___y_2470_ = v___y_2436_;
v___y_2471_ = v___y_2437_;
v___y_2472_ = v___y_2438_;
v___y_2473_ = v___y_2439_;
goto v___jp_2469_;
}
else
{
uint8_t v___x_2500_; lean_object* v___x_2501_; 
lean_dec(v_a_2468_);
lean_del_object(v___x_2465_);
v___x_2500_ = 0;
lean_inc_ref(v_arg_2487_);
v___x_2501_ = l_Lean_Meta_DiscrTree_mkPath(v_arg_2487_, v___x_2500_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v___x_2503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7));
v___x_2504_ = l_Lean_Expr_constLevels_x21(v___x_2497_);
lean_dec_ref(v___x_2497_);
v___x_2505_ = lean_unsigned_to_nat(0u);
v___x_2506_ = l_List_get_x21Internal___redArg(v___x_2433_, v___x_2504_, v___x_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
if (v_isShared_2462_ == 0)
{
lean_ctor_set_tag(v___x_2461_, 1);
lean_ctor_set(v___x_2461_, 1, v___x_2507_);
lean_ctor_set(v___x_2461_, 0, v___x_2506_);
v___x_2509_ = v___x_2461_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = l_Lean_mkConst(v___x_2503_, v___x_2509_);
v___x_2511_ = l_Lean_Expr_app___override(v___x_2510_, v_arg_2494_);
lean_inc(v_fst_2459_);
v___x_2512_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_fst_2459_, v___x_2511_, v_arg_2484_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
v___x_2514_ = 1;
v___x_2515_ = l_Lean_Meta_mkForallFVars(v_fst_2459_, v_arg_2487_, v___x_2500_, v___x_2499_, v___x_2499_, v___x_2514_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v_fst_2459_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2524_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2524_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2524_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2520_, 0, v_a_2502_);
lean_ctor_set(v___x_2520_, 1, v_a_2516_);
lean_ctor_set(v___x_2520_, 2, v_proof_2434_);
lean_ctor_set(v___x_2520_, 3, v_a_2513_);
lean_ctor_set(v___x_2520_, 4, v_prio_2435_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2520_);
v___x_2522_ = v___x_2518_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec(v_a_2513_);
lean_dec(v_a_2502_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v_a_2525_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2515_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2515_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
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
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_a_2502_);
lean_dec_ref(v_arg_2487_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v_a_2533_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2512_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2512_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec_ref(v___x_2497_);
lean_dec_ref(v_arg_2494_);
lean_dec_ref(v_arg_2487_);
lean_dec_ref(v_arg_2484_);
lean_del_object(v___x_2461_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v_a_2542_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2501_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2501_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
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
v___jp_2469_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2474_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1);
v___x_2475_ = l_Lean_indentExpr(v_a_2468_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set_tag(v___x_2465_, 7);
lean_ctor_set(v___x_2465_, 1, v___x_2475_);
lean_ctor_set(v___x_2465_, 0, v___x_2474_);
v___x_2477_ = v___x_2465_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2477_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
return v___x_2478_;
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_del_object(v___x_2465_);
lean_del_object(v___x_2461_);
lean_dec(v_fst_2459_);
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v_a_2550_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2467_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2467_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_prio_2435_);
lean_dec_ref(v_proof_2434_);
v_a_2561_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2456_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2456_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed(lean_object* v_a_2569_, lean_object* v___x_2570_, lean_object* v___x_2571_, lean_object* v___x_2572_, lean_object* v_proof_2573_, lean_object* v_prio_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
uint8_t v___x_3664__boxed_2580_; lean_object* v_res_2581_; 
v___x_3664__boxed_2580_ = lean_unbox(v___x_2571_);
v_res_2581_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(v_a_2569_, v___x_2570_, v___x_3664__boxed_2580_, v___x_2572_, v_proof_2573_, v_prio_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___x_2572_);
return v_res_2581_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0));
v___x_2584_ = l_Lean_stringToMessageData(v___x_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(lean_object* v_type_2585_, lean_object* v_proof_2586_, lean_object* v_prio_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v___x_2593_; lean_object* v_a_2594_; lean_object* v___x_2595_; 
v___x_2593_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_type_2585_, v_a_2589_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc_n(v_a_2594_, 2);
lean_dec_ref(v___x_2593_);
v___x_2595_ = l_Lean_Meta_isProp(v_a_2594_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; uint8_t v___x_2609_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = lean_box(0);
v___x_2609_ = lean_unbox(v_a_2596_);
lean_dec(v_a_2596_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_prio_2587_);
lean_dec_ref(v_proof_2586_);
v___x_2610_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1);
v___x_2611_ = l_Lean_indentExpr(v_a_2594_);
v___x_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2610_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2612_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
else
{
v___y_2599_ = v_a_2588_;
v___y_2600_ = v_a_2589_;
v___y_2601_ = v_a_2590_;
v___y_2602_ = v_a_2591_;
goto v___jp_2598_;
}
v___jp_2598_:
{
lean_object* v___x_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___f_2606_; uint8_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2603_ = lean_box(0);
v___x_2604_ = 0;
v___x_2605_ = lean_box(v___x_2604_);
v___f_2606_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2606_, 0, v_a_2594_);
lean_closure_set(v___f_2606_, 1, v___x_2603_);
lean_closure_set(v___f_2606_, 2, v___x_2605_);
lean_closure_set(v___f_2606_, 3, v___x_2597_);
lean_closure_set(v___f_2606_, 4, v_proof_2586_);
lean_closure_set(v___f_2606_, 5, v_prio_2587_);
v___x_2607_ = 0;
v___x_2608_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_2606_, v___x_2607_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2608_;
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_a_2594_);
lean_dec(v_prio_2587_);
lean_dec_ref(v_proof_2586_);
v_a_2622_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2595_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2595_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___boxed(lean_object* v_type_2630_, lean_object* v_proof_2631_, lean_object* v_prio_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_type_2630_, v_proof_2631_, v_prio_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(lean_object* v_declName_2639_, lean_object* v_prio_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v___x_2646_; 
lean_inc(v_declName_2639_);
v___x_2646_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_2639_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2648_ = l_Lean_ConstantInfo_levelParams(v_a_2647_);
lean_dec(v_a_2647_);
v___x_2649_ = lean_box(0);
v___x_2650_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_2648_, v___x_2649_);
lean_inc(v_declName_2639_);
v___x_2651_ = l_Lean_mkConst(v_declName_2639_, v___x_2650_);
lean_inc(v_a_2644_);
lean_inc_ref(v_a_2643_);
lean_inc(v_a_2642_);
lean_inc_ref(v_a_2641_);
v___x_2652_ = lean_infer_type(v___x_2651_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_declName_2639_);
v___x_2655_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_2653_, v___x_2654_, v_prio_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
return v___x_2655_;
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec(v_prio_2640_);
lean_dec(v_declName_2639_);
v_a_2656_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2652_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2652_);
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
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec(v_prio_2640_);
lean_dec(v_declName_2639_);
v_a_2664_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2646_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2646_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst___boxed(lean_object* v_declName_2672_, lean_object* v_prio_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_2672_, v_prio_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
return v_res_2679_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0));
v___x_2682_ = l_Lean_stringToMessageData(v___x_2681_);
return v___x_2682_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2));
v___x_2685_ = l_Lean_stringToMessageData(v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(lean_object* v_fvar_2686_, lean_object* v_prio_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v___x_2693_; 
lean_inc(v_fvar_2686_);
v___x_2693_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvar_2686_, v_a_2688_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
if (lean_obj_tag(v_a_2694_) == 1)
{
lean_object* v_val_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2704_; 
v_val_2695_ = lean_ctor_get(v_a_2694_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_a_2694_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2697_ = v_a_2694_;
v_isShared_2698_ = v_isSharedCheck_2704_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_val_2695_);
lean_dec(v_a_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2704_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2699_ = l_Lean_LocalDecl_type(v_val_2695_);
lean_dec(v_val_2695_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v_fvar_2686_);
v___x_2701_ = v___x_2697_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_fvar_2686_);
v___x_2701_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; 
v___x_2702_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v___x_2699_, v___x_2701_, v_prio_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2702_;
}
}
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec(v_a_2694_);
lean_dec(v_prio_2687_);
v___x_2705_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1);
v___x_2706_ = l_Lean_MessageData_ofName(v_fvar_2686_);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2709_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2710_;
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v_prio_2687_);
lean_dec(v_fvar_2686_);
v_a_2711_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2693_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2693_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___boxed(lean_object* v_fvar_2719_, lean_object* v_prio_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvar_2719_, v_prio_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; lean_object* v_ngen_2730_; lean_object* v_namePrefix_2731_; lean_object* v_idx_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2761_; 
v___x_2729_ = lean_st_ref_get(v___y_2727_);
v_ngen_2730_ = lean_ctor_get(v___x_2729_, 2);
lean_inc_ref(v_ngen_2730_);
lean_dec(v___x_2729_);
v_namePrefix_2731_ = lean_ctor_get(v_ngen_2730_, 0);
v_idx_2732_ = lean_ctor_get(v_ngen_2730_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_ngen_2730_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2734_ = v_ngen_2730_;
v_isShared_2735_ = v_isSharedCheck_2761_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_idx_2732_);
lean_inc(v_namePrefix_2731_);
lean_dec(v_ngen_2730_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2761_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v_env_2737_; lean_object* v_nextMacroScope_2738_; lean_object* v_auxDeclNGen_2739_; lean_object* v_traceState_2740_; lean_object* v_cache_2741_; lean_object* v_messages_2742_; lean_object* v_infoState_2743_; lean_object* v_snapshotTasks_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2759_; 
v___x_2736_ = lean_st_ref_take(v___y_2727_);
v_env_2737_ = lean_ctor_get(v___x_2736_, 0);
v_nextMacroScope_2738_ = lean_ctor_get(v___x_2736_, 1);
v_auxDeclNGen_2739_ = lean_ctor_get(v___x_2736_, 3);
v_traceState_2740_ = lean_ctor_get(v___x_2736_, 4);
v_cache_2741_ = lean_ctor_get(v___x_2736_, 5);
v_messages_2742_ = lean_ctor_get(v___x_2736_, 6);
v_infoState_2743_ = lean_ctor_get(v___x_2736_, 7);
v_snapshotTasks_2744_ = lean_ctor_get(v___x_2736_, 8);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; 
v_unused_2760_ = lean_ctor_get(v___x_2736_, 2);
lean_dec(v_unused_2760_);
v___x_2746_ = v___x_2736_;
v_isShared_2747_ = v_isSharedCheck_2759_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_snapshotTasks_2744_);
lean_inc(v_infoState_2743_);
lean_inc(v_messages_2742_);
lean_inc(v_cache_2741_);
lean_inc(v_traceState_2740_);
lean_inc(v_auxDeclNGen_2739_);
lean_inc(v_nextMacroScope_2738_);
lean_inc(v_env_2737_);
lean_dec(v___x_2736_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2759_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v_r_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
lean_inc(v_idx_2732_);
lean_inc(v_namePrefix_2731_);
v_r_2748_ = l_Lean_Name_num___override(v_namePrefix_2731_, v_idx_2732_);
v___x_2749_ = lean_unsigned_to_nat(1u);
v___x_2750_ = lean_nat_add(v_idx_2732_, v___x_2749_);
lean_dec(v_idx_2732_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2750_);
v___x_2752_ = v___x_2734_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_namePrefix_2731_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2754_; 
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 2, v___x_2752_);
v___x_2754_ = v___x_2746_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_env_2737_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_nextMacroScope_2738_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v___x_2752_);
lean_ctor_set(v_reuseFailAlloc_2757_, 3, v_auxDeclNGen_2739_);
lean_ctor_set(v_reuseFailAlloc_2757_, 4, v_traceState_2740_);
lean_ctor_set(v_reuseFailAlloc_2757_, 5, v_cache_2741_);
lean_ctor_set(v_reuseFailAlloc_2757_, 6, v_messages_2742_);
lean_ctor_set(v_reuseFailAlloc_2757_, 7, v_infoState_2743_);
lean_ctor_set(v_reuseFailAlloc_2757_, 8, v_snapshotTasks_2744_);
v___x_2754_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_st_ref_set(v___y_2727_, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_r_2748_);
return v___x_2756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg___boxed(lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_2762_);
lean_dec(v___y_2762_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_2768_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___boxed(lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(lean_object* v_ref_2777_, lean_object* v_proof_2778_, lean_object* v_prio_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v___x_2785_; 
lean_inc(v_a_2783_);
lean_inc_ref(v_a_2782_);
lean_inc(v_a_2781_);
lean_inc_ref(v_a_2780_);
lean_inc_ref(v_proof_2778_);
v___x_2785_ = lean_infer_type(v_proof_2778_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v_a_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2787_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v_a_2783_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref(v___x_2787_);
v___x_2789_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2789_, 0, v_a_2788_);
lean_ctor_set(v___x_2789_, 1, v_ref_2777_);
lean_ctor_set(v___x_2789_, 2, v_proof_2778_);
v___x_2790_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_2786_, v___x_2789_, v_prio_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
return v___x_2790_;
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_prio_2779_);
lean_dec_ref(v_proof_2778_);
lean_dec(v_ref_2777_);
v_a_2791_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2785_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2785_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx___boxed(lean_object* v_ref_2799_, lean_object* v_proof_2800_, lean_object* v_prio_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(v_ref_2799_, v_proof_2800_, v_prio_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
return v_res_2807_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2808_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0);
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
return v___x_2812_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
v___x_2814_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
lean_ctor_set(v___x_2814_, 2, v___x_2813_);
lean_ctor_set(v___x_2814_, 3, v___x_2813_);
lean_ctor_set(v___x_2814_, 4, v___x_2813_);
lean_ctor_set(v___x_2814_, 5, v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(lean_object* v_ext_2815_, lean_object* v_b_2816_, uint8_t v_kind_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_currNamespace_2822_; lean_object* v___x_2823_; lean_object* v_env_2824_; lean_object* v_nextMacroScope_2825_; lean_object* v_ngen_2826_; lean_object* v_auxDeclNGen_2827_; lean_object* v_traceState_2828_; lean_object* v_messages_2829_; lean_object* v_infoState_2830_; lean_object* v_snapshotTasks_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2858_; 
v_currNamespace_2822_ = lean_ctor_get(v___y_2819_, 6);
v___x_2823_ = lean_st_ref_take(v___y_2820_);
v_env_2824_ = lean_ctor_get(v___x_2823_, 0);
v_nextMacroScope_2825_ = lean_ctor_get(v___x_2823_, 1);
v_ngen_2826_ = lean_ctor_get(v___x_2823_, 2);
v_auxDeclNGen_2827_ = lean_ctor_get(v___x_2823_, 3);
v_traceState_2828_ = lean_ctor_get(v___x_2823_, 4);
v_messages_2829_ = lean_ctor_get(v___x_2823_, 6);
v_infoState_2830_ = lean_ctor_get(v___x_2823_, 7);
v_snapshotTasks_2831_ = lean_ctor_get(v___x_2823_, 8);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v___x_2823_, 5);
lean_dec(v_unused_2859_);
v___x_2833_ = v___x_2823_;
v_isShared_2834_ = v_isSharedCheck_2858_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_snapshotTasks_2831_);
lean_inc(v_infoState_2830_);
lean_inc(v_messages_2829_);
lean_inc(v_traceState_2828_);
lean_inc(v_auxDeclNGen_2827_);
lean_inc(v_ngen_2826_);
lean_inc(v_nextMacroScope_2825_);
lean_inc(v_env_2824_);
lean_dec(v___x_2823_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2858_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
lean_inc(v_currNamespace_2822_);
v___x_2835_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2824_, v_ext_2815_, v_b_2816_, v_kind_2817_, v_currNamespace_2822_);
v___x_2836_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 5, v___x_2836_);
lean_ctor_set(v___x_2833_, 0, v___x_2835_);
v___x_2838_ = v___x_2833_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_nextMacroScope_2825_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_ngen_2826_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_auxDeclNGen_2827_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_traceState_2828_);
lean_ctor_set(v_reuseFailAlloc_2857_, 5, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2857_, 6, v_messages_2829_);
lean_ctor_set(v_reuseFailAlloc_2857_, 7, v_infoState_2830_);
lean_ctor_set(v_reuseFailAlloc_2857_, 8, v_snapshotTasks_2831_);
v___x_2838_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v_mctx_2841_; lean_object* v_zetaDeltaFVarIds_2842_; lean_object* v_postponed_2843_; lean_object* v_diag_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2855_; 
v___x_2839_ = lean_st_ref_set(v___y_2820_, v___x_2838_);
v___x_2840_ = lean_st_ref_take(v___y_2818_);
v_mctx_2841_ = lean_ctor_get(v___x_2840_, 0);
v_zetaDeltaFVarIds_2842_ = lean_ctor_get(v___x_2840_, 2);
v_postponed_2843_ = lean_ctor_get(v___x_2840_, 3);
v_diag_2844_ = lean_ctor_get(v___x_2840_, 4);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2840_, 1);
lean_dec(v_unused_2856_);
v___x_2846_ = v___x_2840_;
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_diag_2844_);
lean_inc(v_postponed_2843_);
lean_inc(v_zetaDeltaFVarIds_2842_);
lean_inc(v_mctx_2841_);
lean_dec(v___x_2840_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2848_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 1, v___x_2848_);
v___x_2850_ = v___x_2846_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_mctx_2841_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_zetaDeltaFVarIds_2842_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_postponed_2843_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_diag_2844_);
v___x_2850_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = lean_st_ref_set(v___y_2818_, v___x_2850_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___boxed(lean_object* v_ext_2860_, lean_object* v_b_2861_, lean_object* v_kind_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v_kind_boxed_2867_; lean_object* v_res_2868_; 
v_kind_boxed_2867_ = lean_unbox(v_kind_2862_);
v_res_2868_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2860_, v_b_2861_, v_kind_boxed_2867_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(lean_object* v_00_u03b1_2869_, lean_object* v_00_u03b2_2870_, lean_object* v_00_u03c3_2871_, lean_object* v_ext_2872_, lean_object* v_b_2873_, uint8_t v_kind_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2872_, v_b_2873_, v_kind_2874_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___boxed(lean_object* v_00_u03b1_2881_, lean_object* v_00_u03b2_2882_, lean_object* v_00_u03c3_2883_, lean_object* v_ext_2884_, lean_object* v_b_2885_, lean_object* v_kind_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
uint8_t v_kind_boxed_2892_; lean_object* v_res_2893_; 
v_kind_boxed_2892_ = lean_unbox(v_kind_2886_);
v_res_2893_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(v_00_u03b1_2881_, v_00_u03b2_2882_, v_00_u03c3_2883_, v_ext_2884_, v_b_2885_, v_kind_boxed_2892_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(lean_object* v_ext_2894_, lean_object* v_declName_2895_, lean_object* v_prio_2896_, uint8_t v_attrKind_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_2895_, v_prio_2896_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2894_, v_a_2904_, v_attrKind_2897_, v_a_2899_, v_a_2900_, v_a_2901_);
return v___x_2905_;
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v_ext_2894_);
v_a_2906_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2903_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2903_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst___boxed(lean_object* v_ext_2914_, lean_object* v_declName_2915_, lean_object* v_prio_2916_, lean_object* v_attrKind_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
uint8_t v_attrKind_boxed_2923_; lean_object* v_res_2924_; 
v_attrKind_boxed_2923_ = lean_unbox(v_attrKind_2917_);
v_res_2924_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(v_ext_2914_, v_declName_2915_, v_prio_2916_, v_attrKind_boxed_2923_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(lean_object* v_ext_2925_, lean_object* v_fvar_2926_, lean_object* v_prio_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvar_2926_, v_prio_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; uint8_t v___x_2935_; lean_object* v___x_2936_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
v___x_2935_ = 1;
v___x_2936_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2925_, v_a_2934_, v___x_2935_, v_a_2929_, v_a_2930_, v_a_2931_);
return v___x_2936_;
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v_ext_2925_);
v_a_2937_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2933_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2933_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal___boxed(lean_object* v_ext_2945_, lean_object* v_fvar_2946_, lean_object* v_prio_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(v_ext_2945_, v_fvar_2946_, v_prio_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(lean_object* v_x_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2956_, 0, v_a_2955_);
lean_inc_ref_n(v___x_2956_, 2);
v___x_2957_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
lean_ctor_set(v___x_2957_, 2, v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed(lean_object* v_x_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(v_x_2958_, v_a_2959_);
lean_dec_ref(v_x_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(lean_object* v___y_2961_){
_start:
{
lean_inc_ref(v___y_2961_);
return v___y_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed(lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(v___y_2962_);
lean_dec_ref(v___y_2962_);
return v_res_2963_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5(void){
_start:
{
lean_object* v___f_2970_; lean_object* v___f_2971_; lean_object* v___x_2972_; lean_object* v___f_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___f_2970_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1));
v___f_2971_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2));
v___x_2972_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2);
v___f_2973_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0));
v___x_2974_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4));
v___x_2975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
lean_ctor_set(v___x_2975_, 1, v___f_2973_);
lean_ctor_set(v___x_2975_, 2, v___x_2972_);
lean_ctor_set(v___x_2975_, 3, v___f_2971_);
lean_ctor_set(v___x_2975_, 4, v___f_2970_);
return v___x_2975_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt(void){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt;
v___x_2979_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2____boxed(lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
return v_res_2981_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0));
v___x_2984_ = l_Lean_stringToMessageData(v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(lean_object* v_____r_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1);
v___x_2992_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2991_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed(lean_object* v_____r_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(v_____r_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
return v_res_2999_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3000_; double v___x_3001_; 
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3001_ = lean_float_of_nat(v___x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(lean_object* v_cls_3005_, lean_object* v_msg_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_ref_3012_; lean_object* v___x_3013_; lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3058_; 
v_ref_3012_ = lean_ctor_get(v___y_3009_, 5);
v___x_3013_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3058_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3058_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v_traceState_3019_; lean_object* v_env_3020_; lean_object* v_nextMacroScope_3021_; lean_object* v_ngen_3022_; lean_object* v_auxDeclNGen_3023_; lean_object* v_cache_3024_; lean_object* v_messages_3025_; lean_object* v_infoState_3026_; lean_object* v_snapshotTasks_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3057_; 
v___x_3018_ = lean_st_ref_take(v___y_3010_);
v_traceState_3019_ = lean_ctor_get(v___x_3018_, 4);
v_env_3020_ = lean_ctor_get(v___x_3018_, 0);
v_nextMacroScope_3021_ = lean_ctor_get(v___x_3018_, 1);
v_ngen_3022_ = lean_ctor_get(v___x_3018_, 2);
v_auxDeclNGen_3023_ = lean_ctor_get(v___x_3018_, 3);
v_cache_3024_ = lean_ctor_get(v___x_3018_, 5);
v_messages_3025_ = lean_ctor_get(v___x_3018_, 6);
v_infoState_3026_ = lean_ctor_get(v___x_3018_, 7);
v_snapshotTasks_3027_ = lean_ctor_get(v___x_3018_, 8);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3029_ = v___x_3018_;
v_isShared_3030_ = v_isSharedCheck_3057_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_snapshotTasks_3027_);
lean_inc(v_infoState_3026_);
lean_inc(v_messages_3025_);
lean_inc(v_cache_3024_);
lean_inc(v_traceState_3019_);
lean_inc(v_auxDeclNGen_3023_);
lean_inc(v_ngen_3022_);
lean_inc(v_nextMacroScope_3021_);
lean_inc(v_env_3020_);
lean_dec(v___x_3018_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3057_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
uint64_t v_tid_3031_; lean_object* v_traces_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3056_; 
v_tid_3031_ = lean_ctor_get_uint64(v_traceState_3019_, sizeof(void*)*1);
v_traces_3032_ = lean_ctor_get(v_traceState_3019_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_traceState_3019_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3034_ = v_traceState_3019_;
v_isShared_3035_ = v_isSharedCheck_3056_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_traces_3032_);
lean_dec(v_traceState_3019_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3056_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; double v___x_3037_; uint8_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0);
v___x_3038_ = 0;
v___x_3039_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1));
v___x_3040_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3040_, 0, v_cls_3005_);
lean_ctor_set(v___x_3040_, 1, v___x_3036_);
lean_ctor_set(v___x_3040_, 2, v___x_3039_);
lean_ctor_set_float(v___x_3040_, sizeof(void*)*3, v___x_3037_);
lean_ctor_set_float(v___x_3040_, sizeof(void*)*3 + 8, v___x_3037_);
lean_ctor_set_uint8(v___x_3040_, sizeof(void*)*3 + 16, v___x_3038_);
v___x_3041_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2));
v___x_3042_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v_a_3014_);
lean_ctor_set(v___x_3042_, 2, v___x_3041_);
lean_inc(v_ref_3012_);
v___x_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3043_, 0, v_ref_3012_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = l_Lean_PersistentArray_push___redArg(v_traces_3032_, v___x_3043_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3044_);
v___x_3046_ = v___x_3034_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3044_);
lean_ctor_set_uint64(v_reuseFailAlloc_3055_, sizeof(void*)*1, v_tid_3031_);
v___x_3046_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3048_; 
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 4, v___x_3046_);
v___x_3048_ = v___x_3029_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_env_3020_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_nextMacroScope_3021_);
lean_ctor_set(v_reuseFailAlloc_3054_, 2, v_ngen_3022_);
lean_ctor_set(v_reuseFailAlloc_3054_, 3, v_auxDeclNGen_3023_);
lean_ctor_set(v_reuseFailAlloc_3054_, 4, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3054_, 5, v_cache_3024_);
lean_ctor_set(v_reuseFailAlloc_3054_, 6, v_messages_3025_);
lean_ctor_set(v_reuseFailAlloc_3054_, 7, v_infoState_3026_);
lean_ctor_set(v_reuseFailAlloc_3054_, 8, v_snapshotTasks_3027_);
v___x_3048_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3049_ = lean_st_ref_set(v___y_3010_, v___x_3048_);
v___x_3050_ = lean_box(0);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3050_);
v___x_3052_ = v___x_3016_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___boxed(lean_object* v_cls_3059_, lean_object* v_msg_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v_cls_3059_, v_msg_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(lean_object* v_constName_3067_, uint8_t v_skipRealize_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v___x_3074_; lean_object* v_env_3075_; lean_object* v___x_3076_; 
v___x_3074_ = lean_st_ref_get(v___y_3072_);
v_env_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc_ref(v_env_3075_);
lean_dec(v___x_3074_);
lean_inc(v_constName_3067_);
v___x_3076_ = l_Lean_Environment_findAsync_x3f(v_env_3075_, v_constName_3067_, v_skipRealize_3068_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_3067_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
return v___x_3077_;
}
else
{
lean_object* v_val_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_constName_3067_);
v_val_3078_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3076_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_val_3078_);
lean_dec(v___x_3076_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set_tag(v___x_3080_, 0);
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_val_3078_);
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
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0___boxed(lean_object* v_constName_3086_, lean_object* v_skipRealize_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
uint8_t v_skipRealize_boxed_3093_; lean_object* v_res_3094_; 
v_skipRealize_boxed_3093_ = lean_unbox(v_skipRealize_3087_);
v_res_3094_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_constName_3086_, v_skipRealize_boxed_3093_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3094_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3101_; uint64_t v___x_3102_; 
v___x_3101_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0));
v___x_3102_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3101_);
return v___x_3102_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1);
v___x_3104_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0));
v___x_3105_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set_uint64(v___x_3105_, sizeof(void*)*1, v___x_3103_);
return v___x_3105_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3106_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3109_ = lean_box(1);
v___x_3110_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_3111_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
lean_ctor_set(v___x_3112_, 1, v___x_3110_);
lean_ctor_set(v___x_3112_, 2, v___x_3109_);
return v___x_3112_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
lean_ctor_set(v___x_3117_, 2, v___x_3116_);
lean_ctor_set(v___x_3117_, 3, v___x_3116_);
lean_ctor_set(v___x_3117_, 4, v___x_3115_);
lean_ctor_set(v___x_3117_, 5, v___x_3115_);
lean_ctor_set(v___x_3117_, 6, v___x_3115_);
lean_ctor_set(v___x_3117_, 7, v___x_3115_);
lean_ctor_set(v___x_3117_, 8, v___x_3115_);
lean_ctor_set(v___x_3117_, 9, v___x_3115_);
return v___x_3117_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3119_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
lean_ctor_set(v___x_3119_, 2, v___x_3118_);
lean_ctor_set(v___x_3119_, 3, v___x_3118_);
lean_ctor_set(v___x_3119_, 4, v___x_3118_);
lean_ctor_set(v___x_3119_, 5, v___x_3118_);
return v___x_3119_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3120_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
lean_ctor_set(v___x_3121_, 2, v___x_3120_);
lean_ctor_set(v___x_3121_, 3, v___x_3120_);
lean_ctor_set(v___x_3121_, 4, v___x_3120_);
return v___x_3121_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12));
v___x_3127_ = l_Lean_stringToMessageData(v___x_3126_);
return v___x_3127_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_3129_ = l_String_toRawSubstring_x27(v___x_3128_);
return v___x_3129_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17(void){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Array_mkArray0(lean_box(0));
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(lean_object* v___x_3136_, lean_object* v_ext_3137_, lean_object* v___f_3138_, lean_object* v___x_3139_, lean_object* v___x_3140_, lean_object* v___x_3141_, lean_object* v___x_3142_, lean_object* v_declName_3143_, lean_object* v_stx_3144_, uint8_t v_attrKind_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
uint8_t v___x_3149_; uint8_t v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3149_ = 0;
v___x_3150_ = 1;
v___x_3151_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2);
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_3154_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5);
v___x_3155_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6));
v___x_3156_ = lean_box(0);
lean_inc(v___x_3136_);
v___x_3157_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3157_, 0, v___x_3151_);
lean_ctor_set(v___x_3157_, 1, v___x_3136_);
lean_ctor_set(v___x_3157_, 2, v___x_3154_);
lean_ctor_set(v___x_3157_, 3, v___x_3155_);
lean_ctor_set(v___x_3157_, 4, v___x_3156_);
lean_ctor_set(v___x_3157_, 5, v___x_3152_);
lean_ctor_set(v___x_3157_, 6, v___x_3156_);
lean_ctor_set_uint8(v___x_3157_, sizeof(void*)*7, v___x_3149_);
lean_ctor_set_uint8(v___x_3157_, sizeof(void*)*7 + 1, v___x_3149_);
lean_ctor_set_uint8(v___x_3157_, sizeof(void*)*7 + 2, v___x_3149_);
lean_ctor_set_uint8(v___x_3157_, sizeof(void*)*7 + 3, v___x_3150_);
v___x_3158_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7);
v___x_3159_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8);
v___x_3160_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9);
v___x_3161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3158_);
lean_ctor_set(v___x_3161_, 1, v___x_3159_);
lean_ctor_set(v___x_3161_, 2, v___x_3136_);
lean_ctor_set(v___x_3161_, 3, v___x_3153_);
lean_ctor_set(v___x_3161_, 4, v___x_3160_);
v___x_3162_ = lean_st_mk_ref(v___x_3161_);
lean_inc(v_declName_3143_);
v___x_3163_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_declName_3143_, v___x_3149_, v___x_3157_, v___x_3162_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_dec_ref_known(v___x_3163_, 1);
v___x_3164_ = lean_unsigned_to_nat(1u);
v___x_3165_ = l_Lean_Syntax_getArg(v_stx_3144_, v___x_3164_);
lean_inc(v___x_3165_);
v___x_3166_ = l_Lean_getAttrParamOptPrio(v___x_3165_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3262_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3262_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3262_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v___y_3178_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; uint8_t v___y_3186_; lean_object* v___x_3199_; 
v___x_3171_ = lean_box(0);
lean_inc(v_declName_3143_);
v___x_3199_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(v_ext_3137_, v_declName_3143_, v_a_3167_, v_attrKind_3145_, v___x_3157_, v___x_3162_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_dec(v___x_3165_);
lean_dec_ref_known(v___x_3157_, 7);
lean_dec(v_declName_3143_);
lean_dec_ref(v___x_3142_);
lean_dec_ref(v___x_3141_);
lean_dec_ref(v___x_3140_);
lean_dec_ref(v___x_3139_);
lean_dec_ref(v___f_3138_);
v___y_3178_ = v___x_3199_;
goto v___jp_3177_;
}
else
{
lean_object* v_a_3200_; uint8_t v___y_3202_; uint8_t v___x_3260_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
v___x_3260_ = l_Lean_Exception_isInterrupt(v_a_3200_);
if (v___x_3260_ == 0)
{
uint8_t v___x_3261_; 
v___x_3261_ = l_Lean_Exception_isRuntime(v_a_3200_);
v___y_3202_ = v___x_3261_;
goto v___jp_3201_;
}
else
{
lean_dec(v_a_3200_);
v___y_3202_ = v___x_3260_;
goto v___jp_3201_;
}
v___jp_3201_:
{
if (v___y_3202_ == 0)
{
lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3258_; 
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v___x_3199_, 0);
lean_dec(v_unused_3259_);
v___x_3204_ = v___x_3199_;
v_isShared_3205_ = v_isSharedCheck_3258_;
goto v_resetjp_3203_;
}
else
{
lean_dec(v___x_3199_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3258_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_3207_ = l_Lean_getBuiltinAttributeImpl(v___x_3206_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v_options_3209_; lean_object* v_ref_3210_; lean_object* v_quotContext_3211_; lean_object* v_currMacroScope_3212_; lean_object* v_inheritedTraceOptions_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v_add_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3240_; 
lean_del_object(v___x_3204_);
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v_options_3209_ = lean_ctor_get(v___y_3146_, 2);
v_ref_3210_ = lean_ctor_get(v___y_3146_, 5);
v_quotContext_3211_ = lean_ctor_get(v___y_3146_, 10);
v_currMacroScope_3212_ = lean_ctor_get(v___y_3146_, 11);
v_inheritedTraceOptions_3213_ = lean_ctor_get(v___y_3146_, 13);
v___x_3214_ = l_Lean_SourceInfo_fromRef(v_ref_3210_, v___y_3202_);
v___x_3215_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14);
lean_inc(v_currMacroScope_3212_);
lean_inc(v_quotContext_3211_);
v___x_3216_ = l_Lean_addMacroScope(v_quotContext_3211_, v___x_3206_, v_currMacroScope_3212_);
v___x_3217_ = lean_box(0);
lean_inc(v___x_3214_);
v___x_3218_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3214_);
lean_ctor_set(v___x_3218_, 1, v___x_3215_);
lean_ctor_set(v___x_3218_, 2, v___x_3216_);
lean_ctor_set(v___x_3218_, 3, v___x_3217_);
v_add_3219_ = lean_ctor_get(v_a_3208_, 1);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_a_3208_);
if (v_isSharedCheck_3240_ == 0)
{
lean_object* v_unused_3241_; lean_object* v_unused_3242_; 
v_unused_3241_ = lean_ctor_get(v_a_3208_, 2);
lean_dec(v_unused_3241_);
v_unused_3242_ = lean_ctor_get(v_a_3208_, 0);
lean_dec(v_unused_3242_);
v___x_3221_ = v_a_3208_;
v_isShared_3222_ = v_isSharedCheck_3240_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_add_3219_);
lean_dec(v_a_3208_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3240_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3223_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16));
v___x_3224_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17);
lean_inc(v___x_3214_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 2, v___x_3224_);
lean_ctor_set(v___x_3221_, 1, v___x_3223_);
lean_ctor_set(v___x_3221_, 0, v___x_3214_);
v___x_3226_ = v___x_3221_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3239_, 2, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3227_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18));
v___x_3228_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3229_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19));
v___x_3230_ = l_Lean_Name_mkStr4(v___x_3142_, v___x_3227_, v___x_3228_, v___x_3229_);
v___x_3231_ = l_Lean_Syntax_node2(v___x_3214_, v___x_3230_, v___x_3218_, v___x_3226_);
v___x_3232_ = lean_unsigned_to_nat(3u);
v___x_3233_ = l_Lean_Syntax_setArg(v___x_3231_, v___x_3232_, v___x_3165_);
v___x_3234_ = lean_box(v_attrKind_3145_);
lean_inc(v___y_3147_);
lean_inc_ref(v___y_3146_);
v___x_3235_ = lean_apply_6(v_add_3219_, v_declName_3143_, v___x_3233_, v___x_3234_, v___y_3146_, v___y_3147_, lean_box(0));
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_dec_ref_known(v___x_3235_, 1);
lean_dec_ref_known(v___x_3157_, 7);
lean_dec_ref(v___x_3141_);
lean_dec_ref(v___x_3140_);
lean_dec_ref(v___x_3139_);
lean_dec_ref(v___f_3138_);
goto v___jp_3172_;
}
else
{
lean_object* v_a_3236_; uint8_t v___x_3237_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
v___x_3237_ = l_Lean_Exception_isInterrupt(v_a_3236_);
if (v___x_3237_ == 0)
{
uint8_t v___x_3238_; 
lean_inc(v_a_3236_);
v___x_3238_ = l_Lean_Exception_isRuntime(v_a_3236_);
v___y_3182_ = v_inheritedTraceOptions_3213_;
v___y_3183_ = v_options_3209_;
v___y_3184_ = v___x_3235_;
v___y_3185_ = v_a_3236_;
v___y_3186_ = v___x_3238_;
goto v___jp_3181_;
}
else
{
v___y_3182_ = v_inheritedTraceOptions_3213_;
v___y_3183_ = v_options_3209_;
v___y_3184_ = v___x_3235_;
v___y_3185_ = v_a_3236_;
v___y_3186_ = v___x_3237_;
goto v___jp_3181_;
}
}
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3257_; 
lean_del_object(v___x_3169_);
lean_dec(v___x_3165_);
lean_dec(v___x_3162_);
lean_dec_ref_known(v___x_3157_, 7);
lean_dec(v_declName_3143_);
lean_dec_ref(v___x_3142_);
lean_dec_ref(v___x_3141_);
lean_dec_ref(v___x_3140_);
lean_dec_ref(v___x_3139_);
lean_dec_ref(v___f_3138_);
v_a_3243_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3245_ = v___x_3207_;
v_isShared_3246_ = v_isSharedCheck_3257_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3207_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3257_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v_ref_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v_ref_3247_ = lean_ctor_get(v___y_3146_, 5);
v___x_3248_ = lean_io_error_to_string(v_a_3243_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 3);
lean_ctor_set(v___x_3204_, 0, v___x_3248_);
v___x_3250_ = v___x_3204_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3251_ = l_Lean_MessageData_ofFormat(v___x_3250_);
lean_inc(v_ref_3247_);
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v_ref_3247_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3252_);
v___x_3254_ = v___x_3245_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3165_);
lean_dec_ref_known(v___x_3157_, 7);
lean_dec(v_declName_3143_);
lean_dec_ref(v___x_3142_);
lean_dec_ref(v___x_3141_);
lean_dec_ref(v___x_3140_);
lean_dec_ref(v___x_3139_);
lean_dec_ref(v___f_3138_);
v___y_3178_ = v___x_3199_;
goto v___jp_3177_;
}
}
}
v___jp_3172_:
{
lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3173_ = lean_st_ref_get(v___x_3162_);
lean_dec(v___x_3162_);
lean_dec(v___x_3173_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v___x_3171_);
v___x_3175_ = v___x_3169_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3171_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
v___jp_3177_:
{
if (lean_obj_tag(v___y_3178_) == 0)
{
lean_dec_ref_known(v___y_3178_, 1);
goto v___jp_3172_;
}
else
{
lean_del_object(v___x_3169_);
lean_dec(v___x_3162_);
return v___y_3178_;
}
}
v___jp_3179_:
{
lean_object* v___x_3180_; 
lean_inc(v___y_3147_);
lean_inc_ref(v___y_3146_);
lean_inc(v___x_3162_);
v___x_3180_ = lean_apply_6(v___f_3138_, v___x_3171_, v___x_3157_, v___x_3162_, v___y_3146_, v___y_3147_, lean_box(0));
v___y_3178_ = v___x_3180_;
goto v___jp_3177_;
}
v___jp_3181_:
{
if (v___y_3186_ == 0)
{
uint8_t v_hasTrace_3187_; 
lean_dec_ref(v___y_3184_);
v_hasTrace_3187_ = lean_ctor_get_uint8(v___y_3183_, sizeof(void*)*1);
if (v_hasTrace_3187_ == 0)
{
lean_dec_ref(v___y_3185_);
lean_dec_ref(v___x_3141_);
lean_dec_ref(v___x_3140_);
lean_dec_ref(v___x_3139_);
goto v___jp_3179_;
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v___x_3188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3189_ = l_Lean_Name_mkStr4(v___x_3139_, v___x_3140_, v___x_3141_, v___x_3188_);
v___x_3190_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11));
lean_inc(v___x_3189_);
v___x_3191_ = l_Lean_Name_append(v___x_3190_, v___x_3189_);
v___x_3192_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_3182_, v___y_3183_, v___x_3191_);
lean_dec(v___x_3191_);
if (v___x_3192_ == 0)
{
lean_dec(v___x_3189_);
lean_dec_ref(v___y_3185_);
goto v___jp_3179_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3193_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13);
v___x_3194_ = l_Lean_Exception_toMessageData(v___y_3185_);
v___x_3195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3193_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v___x_3189_, v___x_3195_, v___x_3157_, v___x_3162_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
lean_inc(v___y_3147_);
lean_inc_ref(v___y_3146_);
lean_inc(v___x_3162_);
v___x_3198_ = lean_apply_6(v___f_3138_, v_a_3197_, v___x_3157_, v___x_3162_, v___y_3146_, v___y_3147_, lean_box(0));
v___y_3178_ = v___x_3198_;
goto v___jp_3177_;
}
else
{
lean_dec_ref_known(v___x_3157_, 7);
lean_dec_ref(v___f_3138_);
v___y_3178_ = v___x_3196_;
goto v___jp_3177_;
}
}
}
}
else
{
lean_dec_ref(v___y_3185_);
lean_del_object(v___x_3169_);
lean_dec(v___x_3162_);
lean_dec_ref_known(v___x_3157_, 7);
lean_dec_ref(v___x_3141_);
lean_dec_ref(v___x_3140_);
lean_dec_ref(v___x_3139_);
lean_dec_ref(v___f_3138_);
return v___y_3184_;
}
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec(v___x_3165_);
lean_dec(v___x_3162_);
lean_dec_ref_known(v___x_3157_, 7);
lean_dec(v_declName_3143_);
lean_dec_ref(v___x_3142_);
lean_dec_ref(v___x_3141_);
lean_dec_ref(v___x_3140_);
lean_dec_ref(v___x_3139_);
lean_dec_ref(v___f_3138_);
lean_dec_ref(v_ext_3137_);
v_a_3263_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3166_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3166_);
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
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v___x_3162_);
lean_dec_ref_known(v___x_3157_, 7);
lean_dec(v_declName_3143_);
lean_dec_ref(v___x_3142_);
lean_dec_ref(v___x_3141_);
lean_dec_ref(v___x_3140_);
lean_dec_ref(v___x_3139_);
lean_dec_ref(v___f_3138_);
lean_dec_ref(v_ext_3137_);
v_a_3271_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3163_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3163_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed(lean_object* v___x_3279_, lean_object* v_ext_3280_, lean_object* v___f_3281_, lean_object* v___x_3282_, lean_object* v___x_3283_, lean_object* v___x_3284_, lean_object* v___x_3285_, lean_object* v_declName_3286_, lean_object* v_stx_3287_, lean_object* v_attrKind_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
uint8_t v_attrKind_boxed_3292_; lean_object* v_res_3293_; 
v_attrKind_boxed_3292_ = lean_unbox(v_attrKind_3288_);
v_res_3293_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(v___x_3279_, v_ext_3280_, v___f_3281_, v___x_3282_, v___x_3283_, v___x_3284_, v___x_3285_, v_declName_3286_, v_stx_3287_, v_attrKind_boxed_3292_, v___y_3289_, v___y_3290_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v_stx_3287_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(lean_object* v_msgData_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v___x_3298_; lean_object* v_env_3299_; lean_object* v_options_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3298_ = lean_st_ref_get(v___y_3296_);
v_env_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc_ref(v_env_3299_);
lean_dec(v___x_3298_);
v_options_3300_ = lean_ctor_get(v___y_3295_, 2);
v___x_3301_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_3302_ = lean_unsigned_to_nat(32u);
v___x_3303_ = lean_mk_empty_array_with_capacity(v___x_3302_);
lean_dec_ref(v___x_3303_);
v___x_3304_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
lean_inc_ref(v_options_3300_);
v___x_3305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3305_, 0, v_env_3299_);
lean_ctor_set(v___x_3305_, 1, v___x_3301_);
lean_ctor_set(v___x_3305_, 2, v___x_3304_);
lean_ctor_set(v___x_3305_, 3, v_options_3300_);
v___x_3306_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
lean_ctor_set(v___x_3306_, 1, v_msgData_3294_);
v___x_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2___boxed(lean_object* v_msgData_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msgData_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(lean_object* v_msg_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_ref_3317_; lean_object* v___x_3318_; lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3327_; 
v_ref_3317_ = lean_ctor_get(v___y_3314_, 5);
v___x_3318_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msg_3313_, v___y_3314_, v___y_3315_);
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3327_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3327_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; lean_object* v___x_3325_; 
lean_inc(v_ref_3317_);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v_ref_3317_);
lean_ctor_set(v___x_3323_, 1, v_a_3319_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set_tag(v___x_3321_, 1);
lean_ctor_set(v___x_3321_, 0, v___x_3323_);
v___x_3325_ = v___x_3321_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg___boxed(lean_object* v_msg_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v_msg_3328_, v___y_3329_, v___y_3330_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
return v_res_3332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0));
v___x_3335_ = l_Lean_stringToMessageData(v___x_3334_);
return v___x_3335_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2));
v___x_3338_ = l_Lean_stringToMessageData(v___x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(lean_object* v___x_3339_, lean_object* v_decl_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3344_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1);
v___x_3345_ = l_Lean_MessageData_ofName(v___x_3339_);
v___x_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3344_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v___x_3348_, v___y_3341_, v___y_3342_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed(lean_object* v___x_3350_, lean_object* v_decl_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(v___x_3350_, v_decl_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v_decl_3351_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(lean_object* v_ext_3376_){
_start:
{
lean_object* v___f_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___f_3377_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0));
v___x_3378_ = lean_box(1);
v___x_3379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___f_3383_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3383_, 0, v___x_3378_);
lean_closure_set(v___f_3383_, 1, v_ext_3376_);
lean_closure_set(v___f_3383_, 2, v___f_3377_);
lean_closure_set(v___f_3383_, 3, v___x_3380_);
lean_closure_set(v___f_3383_, 4, v___x_3381_);
lean_closure_set(v___f_3383_, 5, v___x_3382_);
lean_closure_set(v___f_3383_, 6, v___x_3379_);
v___f_3384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5));
v___x_3385_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7));
v___x_3386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v___f_3383_);
lean_ctor_set(v___x_3386_, 2, v___f_3384_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(lean_object* v_00_u03b1_3387_, lean_object* v_msg_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v_msg_3388_, v___y_3389_, v___y_3390_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___boxed(lean_object* v_00_u03b1_3393_, lean_object* v_msg_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(v_00_u03b1_3393_, v_msg_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
return v_res_3398_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
v___x_3400_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(v___x_3399_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_);
v___x_3403_ = l_Lean_registerBuiltinAttribute(v___x_3402_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2____boxed(lean_object* v_a_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(lean_object* v_ext_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v___x_3409_; lean_object* v_ext_3410_; lean_object* v_toEnvExtension_3411_; lean_object* v_env_3412_; lean_object* v_asyncMode_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3409_ = lean_st_ref_get(v_a_3407_);
v_ext_3410_ = lean_ctor_get(v_ext_3406_, 1);
v_toEnvExtension_3411_ = lean_ctor_get(v_ext_3410_, 0);
v_env_3412_ = lean_ctor_get(v___x_3409_, 0);
lean_inc_ref(v_env_3412_);
lean_dec(v___x_3409_);
v_asyncMode_3413_ = lean_ctor_get(v_toEnvExtension_3411_, 2);
v___x_3414_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
v___x_3415_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3414_, v_ext_3406_, v_env_3412_, v_asyncMode_3413_);
v___x_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg___boxed(lean_object* v_ext_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_3417_, v_a_3418_);
lean_dec(v_a_3418_);
lean_dec_ref(v_ext_3417_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(lean_object* v_ext_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v___x_3425_; 
v___x_3425_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_3421_, v_a_3423_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___boxed(lean_object* v_ext_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(v_ext_3426_, v_a_3427_, v_a_3428_);
lean_dec(v_a_3428_);
lean_dec_ref(v_a_3427_);
lean_dec_ref(v_ext_3426_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(lean_object* v_a_3431_){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
v___x_3434_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v___x_3433_, v_a_3431_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg___boxed(lean_object* v_a_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3435_);
lean_dec(v_a_3435_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3439_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___boxed(lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(v_a_3442_, v_a_3443_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(lean_object* v_x_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object* v_x_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(v_x_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v_x_3452_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___f_3471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3475_ = 0;
v___x_3476_ = lean_box(2);
v___x_3477_ = l_Lean_registerTagAttribute(v___x_3472_, v___x_3473_, v___f_3471_, v___x_3474_, v___x_3475_, v___x_3476_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object* v_a_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
return v_res_3479_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(lean_object* v_env_3480_, lean_object* v_ty_3481_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_Expr_getAppFn(v_ty_3481_);
if (lean_obj_tag(v___x_3482_) == 4)
{
lean_object* v_declName_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v_declName_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_declName_3483_);
lean_dec_ref_known(v___x_3482_, 2);
v___x_3484_ = l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr;
v___x_3485_ = l_Lean_TagAttribute_hasTag(v___x_3484_, v_env_3480_, v_declName_3483_);
return v___x_3485_;
}
else
{
uint8_t v___x_3486_; 
lean_dec_ref(v___x_3482_);
lean_dec_ref(v_env_3480_);
v___x_3486_ = 0;
return v___x_3486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType___boxed(lean_object* v_env_3487_, lean_object* v_ty_3488_){
_start:
{
uint8_t v_res_3489_; lean_object* v_r_3490_; 
v_res_3489_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v_env_3487_, v_ty_3488_);
lean_dec_ref(v_ty_3488_);
v_r_3490_ = lean_box(v_res_3489_);
return v_r_3490_;
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
