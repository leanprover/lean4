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
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mvcgen_simp"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 132, 230, 222, 36, 150, 155, 178)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "simp theorems internally used by `mvcgen`"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mvcgenSimpExt"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 109, 122, 82, 215, 148, 2, 116)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(15, 64, 145, 249, 56, 70, 6, 95)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2____boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__3;
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
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "spec_invariant_type"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 116, 165, 165, 49, 205, 9, 77)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "marks a type as an invariant type for the `mvcgen` tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "specInvariantAttr"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 109, 122, 82, 215, 148, 2, 116)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 249, 139, 62, 184, 94, 1, 139)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_108_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_109_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_110_ = l_Lean_Meta_registerSimpAttr(v___x_107_, v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2____boxed(lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_();
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
v___x_311_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
lean_ctor_set(v___x_311_, 3, v___x_309_);
lean_ctor_set(v___x_311_, 4, v___x_309_);
lean_ctor_set(v___x_311_, 5, v___x_309_);
lean_ctor_set(v___x_311_, 6, v___x_309_);
lean_ctor_set(v___x_311_, 7, v___x_309_);
lean_ctor_set(v___x_311_, 8, v___x_309_);
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
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default));
v___x_866_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0));
v___x_868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v___x_866_);
lean_ctor_set(v___x_868_, 2, v___x_865_);
lean_ctor_set(v___x_868_, 3, v___x_864_);
lean_ctor_set(v___x_868_, 4, v___x_864_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default(void){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem(void){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default;
return v___x_870_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(lean_object* v_xs_871_, lean_object* v_ys_872_, lean_object* v_x_873_){
_start:
{
lean_object* v_zero_874_; uint8_t v_isZero_875_; 
v_zero_874_ = lean_unsigned_to_nat(0u);
v_isZero_875_ = lean_nat_dec_eq(v_x_873_, v_zero_874_);
if (v_isZero_875_ == 1)
{
lean_dec(v_x_873_);
return v_isZero_875_;
}
else
{
lean_object* v_one_876_; lean_object* v_n_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_one_876_ = lean_unsigned_to_nat(1u);
v_n_877_ = lean_nat_sub(v_x_873_, v_one_876_);
lean_dec(v_x_873_);
v___x_878_ = lean_array_fget_borrowed(v_xs_871_, v_n_877_);
v___x_879_ = lean_array_fget_borrowed(v_ys_872_, v_n_877_);
v___x_880_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_dec(v_n_877_);
return v___x_880_;
}
else
{
v_x_873_ = v_n_877_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg___boxed(lean_object* v_xs_882_, lean_object* v_ys_883_, lean_object* v_x_884_){
_start:
{
uint8_t v_res_885_; lean_object* v_r_886_; 
v_res_885_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_xs_882_, v_ys_883_, v_x_884_);
lean_dec_ref(v_ys_883_);
lean_dec_ref(v_xs_882_);
v_r_886_ = lean_box(v_res_885_);
return v_r_886_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
lean_object* v_keys_889_; lean_object* v_prog_890_; lean_object* v_proof_891_; lean_object* v_etaPotential_892_; lean_object* v_priority_893_; lean_object* v_keys_894_; lean_object* v_prog_895_; lean_object* v_proof_896_; lean_object* v_etaPotential_897_; lean_object* v_priority_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v_keys_889_ = lean_ctor_get(v_x_887_, 0);
lean_inc_ref(v_keys_889_);
v_prog_890_ = lean_ctor_get(v_x_887_, 1);
lean_inc_ref(v_prog_890_);
v_proof_891_ = lean_ctor_get(v_x_887_, 2);
lean_inc_ref(v_proof_891_);
v_etaPotential_892_ = lean_ctor_get(v_x_887_, 3);
lean_inc(v_etaPotential_892_);
v_priority_893_ = lean_ctor_get(v_x_887_, 4);
lean_inc(v_priority_893_);
lean_dec_ref(v_x_887_);
v_keys_894_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_keys_894_);
v_prog_895_ = lean_ctor_get(v_x_888_, 1);
lean_inc_ref(v_prog_895_);
v_proof_896_ = lean_ctor_get(v_x_888_, 2);
lean_inc_ref(v_proof_896_);
v_etaPotential_897_ = lean_ctor_get(v_x_888_, 3);
lean_inc(v_etaPotential_897_);
v_priority_898_ = lean_ctor_get(v_x_888_, 4);
lean_inc(v_priority_898_);
lean_dec_ref(v_x_888_);
v___x_899_ = lean_array_get_size(v_keys_889_);
v___x_900_ = lean_array_get_size(v_keys_894_);
v___x_901_ = lean_nat_dec_eq(v___x_899_, v___x_900_);
if (v___x_901_ == 0)
{
lean_dec(v_priority_898_);
lean_dec(v_etaPotential_897_);
lean_dec_ref(v_proof_896_);
lean_dec_ref(v_prog_895_);
lean_dec_ref(v_keys_894_);
lean_dec(v_priority_893_);
lean_dec(v_etaPotential_892_);
lean_dec_ref(v_proof_891_);
lean_dec_ref(v_prog_890_);
lean_dec_ref(v_keys_889_);
return v___x_901_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_keys_889_, v_keys_894_, v___x_899_);
lean_dec_ref(v_keys_894_);
lean_dec_ref(v_keys_889_);
if (v___x_902_ == 0)
{
lean_dec(v_priority_898_);
lean_dec(v_etaPotential_897_);
lean_dec_ref(v_proof_896_);
lean_dec_ref(v_prog_895_);
lean_dec(v_priority_893_);
lean_dec(v_etaPotential_892_);
lean_dec_ref(v_proof_891_);
lean_dec_ref(v_prog_890_);
return v___x_902_;
}
else
{
uint8_t v___x_903_; 
v___x_903_ = lean_expr_eqv(v_prog_890_, v_prog_895_);
lean_dec_ref(v_prog_895_);
lean_dec_ref(v_prog_890_);
if (v___x_903_ == 0)
{
lean_dec(v_priority_898_);
lean_dec(v_etaPotential_897_);
lean_dec_ref(v_proof_896_);
lean_dec(v_priority_893_);
lean_dec(v_etaPotential_892_);
lean_dec_ref(v_proof_891_);
return v___x_903_;
}
else
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_proof_891_, v_proof_896_);
if (v___x_904_ == 0)
{
lean_dec(v_priority_898_);
lean_dec(v_etaPotential_897_);
lean_dec(v_priority_893_);
lean_dec(v_etaPotential_892_);
return v___x_904_;
}
else
{
uint8_t v___x_905_; 
v___x_905_ = lean_nat_dec_eq(v_etaPotential_892_, v_etaPotential_897_);
lean_dec(v_etaPotential_897_);
lean_dec(v_etaPotential_892_);
if (v___x_905_ == 0)
{
lean_dec(v_priority_898_);
lean_dec(v_priority_893_);
return v___x_905_;
}
else
{
uint8_t v___x_906_; 
v___x_906_ = lean_nat_dec_eq(v_priority_893_, v_priority_898_);
lean_dec(v_priority_898_);
lean_dec(v_priority_893_);
return v___x_906_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq___boxed(lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
uint8_t v_res_909_; lean_object* v_r_910_; 
v_res_909_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(v_x_907_, v_x_908_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(lean_object* v_xs_911_, lean_object* v_ys_912_, lean_object* v_hsz_913_, lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_xs_911_, v_ys_912_, v_x_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___boxed(lean_object* v_xs_917_, lean_object* v_ys_918_, lean_object* v_hsz_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(v_xs_917_, v_ys_918_, v_hsz_919_, v_x_920_, v_x_921_);
lean_dec_ref(v_ys_918_);
lean_dec_ref(v_xs_917_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_926_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(lean_object* v_00_u03b2_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(lean_box(0));
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__3(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2);
v___x_936_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default(void){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__3);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems(void){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
lean_object* v_ks_944_; lean_object* v_vs_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_969_; 
v_ks_944_ = lean_ctor_get(v_x_940_, 0);
v_vs_945_ = lean_ctor_get(v_x_940_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_940_);
if (v_isSharedCheck_969_ == 0)
{
v___x_947_ = v_x_940_;
v_isShared_948_ = v_isSharedCheck_969_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_vs_945_);
lean_inc(v_ks_944_);
lean_dec(v_x_940_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_969_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_array_get_size(v_ks_944_);
v___x_950_ = lean_nat_dec_lt(v_x_941_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
lean_dec(v_x_941_);
v___x_951_ = lean_array_push(v_ks_944_, v_x_942_);
v___x_952_ = lean_array_push(v_vs_945_, v_x_943_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_952_);
lean_ctor_set(v___x_947_, 0, v___x_951_);
v___x_954_ = v___x_947_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
else
{
lean_object* v_k_x27_956_; uint8_t v___x_957_; 
v_k_x27_956_ = lean_array_fget_borrowed(v_ks_944_, v_x_941_);
v___x_957_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_942_, v_k_x27_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_959_; 
if (v_isShared_948_ == 0)
{
v___x_959_ = v___x_947_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_ks_944_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_vs_945_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_x_941_, v___x_960_);
lean_dec(v_x_941_);
v_x_940_ = v___x_959_;
v_x_941_ = v___x_961_;
goto _start;
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_964_ = lean_array_fset(v_ks_944_, v_x_941_, v_x_942_);
v___x_965_ = lean_array_fset(v_vs_945_, v_x_941_, v_x_943_);
lean_dec(v_x_941_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_965_);
lean_ctor_set(v___x_947_, 0, v___x_964_);
v___x_967_ = v___x_947_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_n_970_, lean_object* v_k_971_, lean_object* v_v_972_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_n_970_, v___x_973_, v_k_971_, v_v_972_);
return v___x_974_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_975_; size_t v___x_976_; size_t v___x_977_; 
v___x_975_ = ((size_t)5ULL);
v___x_976_ = ((size_t)1ULL);
v___x_977_ = lean_usize_shift_left(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_978_; size_t v___x_979_; size_t v___x_980_; 
v___x_978_ = ((size_t)1ULL);
v___x_979_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_980_ = lean_usize_sub(v___x_979_, v___x_978_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(lean_object* v_x_982_, size_t v_x_983_, size_t v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
if (lean_obj_tag(v_x_982_) == 0)
{
lean_object* v_es_987_; size_t v___x_988_; size_t v___x_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v_j_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_es_987_ = lean_ctor_get(v_x_982_, 0);
v___x_988_ = ((size_t)5ULL);
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_991_ = lean_usize_land(v_x_983_, v___x_990_);
v_j_992_ = lean_usize_to_nat(v___x_991_);
v___x_993_ = lean_array_get_size(v_es_987_);
v___x_994_ = lean_nat_dec_lt(v_j_992_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec(v_j_992_);
lean_dec(v_x_986_);
lean_dec(v_x_985_);
return v_x_982_;
}
else
{
lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1031_; 
lean_inc_ref(v_es_987_);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_x_982_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v_x_982_, 0);
lean_dec(v_unused_1032_);
v___x_996_ = v_x_982_;
v_isShared_997_ = v_isSharedCheck_1031_;
goto v_resetjp_995_;
}
else
{
lean_dec(v_x_982_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1031_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_v_998_; lean_object* v___x_999_; lean_object* v_xs_x27_1000_; lean_object* v___y_1002_; 
v_v_998_ = lean_array_fget(v_es_987_, v_j_992_);
v___x_999_ = lean_box(0);
v_xs_x27_1000_ = lean_array_fset(v_es_987_, v_j_992_, v___x_999_);
switch(lean_obj_tag(v_v_998_))
{
case 0:
{
lean_object* v_key_1007_; lean_object* v_val_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1018_; 
v_key_1007_ = lean_ctor_get(v_v_998_, 0);
v_val_1008_ = lean_ctor_get(v_v_998_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_v_998_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1010_ = v_v_998_;
v_isShared_1011_ = v_isSharedCheck_1018_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_val_1008_);
lean_inc(v_key_1007_);
lean_dec(v_v_998_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1018_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_985_, v_key_1007_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_del_object(v___x_1010_);
v___x_1013_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1007_, v_val_1008_, v_x_985_, v_x_986_);
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
v___y_1002_ = v___x_1014_;
goto v___jp_1001_;
}
else
{
lean_object* v___x_1016_; 
lean_dec(v_val_1008_);
lean_dec(v_key_1007_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v_x_986_);
lean_ctor_set(v___x_1010_, 0, v_x_985_);
v___x_1016_ = v___x_1010_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_x_985_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_x_986_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
v___y_1002_ = v___x_1016_;
goto v___jp_1001_;
}
}
}
}
case 1:
{
lean_object* v_node_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1029_; 
v_node_1019_ = lean_ctor_get(v_v_998_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_v_998_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1021_ = v_v_998_;
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_node_1019_);
lean_dec(v_v_998_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1023_ = lean_usize_shift_right(v_x_983_, v___x_988_);
v___x_1024_ = lean_usize_add(v_x_984_, v___x_989_);
v___x_1025_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_node_1019_, v___x_1023_, v___x_1024_, v_x_985_, v_x_986_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1025_);
v___x_1027_ = v___x_1021_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
v___y_1002_ = v___x_1027_;
goto v___jp_1001_;
}
}
}
default: 
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_x_985_);
lean_ctor_set(v___x_1030_, 1, v_x_986_);
v___y_1002_ = v___x_1030_;
goto v___jp_1001_;
}
}
v___jp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_array_fset(v_xs_x27_1000_, v_j_992_, v___y_1002_);
lean_dec(v_j_992_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1003_);
v___x_1005_ = v___x_996_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
else
{
lean_object* v_ks_1033_; lean_object* v_vs_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1054_; 
v_ks_1033_ = lean_ctor_get(v_x_982_, 0);
v_vs_1034_ = lean_ctor_get(v_x_982_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_982_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1036_ = v_x_982_;
v_isShared_1037_ = v_isSharedCheck_1054_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_vs_1034_);
lean_inc(v_ks_1033_);
lean_dec(v_x_982_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1054_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_ks_1033_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_vs_1034_);
v___x_1039_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v_newNode_1040_; uint8_t v___y_1042_; size_t v___x_1048_; uint8_t v___x_1049_; 
v_newNode_1040_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(v___x_1039_, v_x_985_, v_x_986_);
v___x_1048_ = ((size_t)7ULL);
v___x_1049_ = lean_usize_dec_le(v___x_1048_, v_x_984_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1050_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1040_);
v___x_1051_ = lean_unsigned_to_nat(4u);
v___x_1052_ = lean_nat_dec_lt(v___x_1050_, v___x_1051_);
lean_dec(v___x_1050_);
v___y_1042_ = v___x_1052_;
goto v___jp_1041_;
}
else
{
v___y_1042_ = v___x_1049_;
goto v___jp_1041_;
}
v___jp_1041_:
{
if (v___y_1042_ == 0)
{
lean_object* v_ks_1043_; lean_object* v_vs_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_ks_1043_ = lean_ctor_get(v_newNode_1040_, 0);
lean_inc_ref(v_ks_1043_);
v_vs_1044_ = lean_ctor_get(v_newNode_1040_, 1);
lean_inc_ref(v_vs_1044_);
lean_dec_ref(v_newNode_1040_);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2);
v___x_1047_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_x_984_, v_ks_1043_, v_vs_1044_, v___x_1045_, v___x_1046_);
lean_dec_ref(v_vs_1044_);
lean_dec_ref(v_ks_1043_);
return v___x_1047_;
}
else
{
return v_newNode_1040_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(size_t v_depth_1055_, lean_object* v_keys_1056_, lean_object* v_vals_1057_, lean_object* v_i_1058_, lean_object* v_entries_1059_){
_start:
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_array_get_size(v_keys_1056_);
v___x_1061_ = lean_nat_dec_lt(v_i_1058_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec(v_i_1058_);
return v_entries_1059_;
}
else
{
lean_object* v_k_1062_; lean_object* v_v_1063_; uint64_t v___x_1064_; size_t v_h_1065_; size_t v___x_1066_; lean_object* v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; size_t v_h_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_k_1062_ = lean_array_fget_borrowed(v_keys_1056_, v_i_1058_);
v_v_1063_ = lean_array_fget_borrowed(v_vals_1057_, v_i_1058_);
v___x_1064_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1062_);
v_h_1065_ = lean_uint64_to_usize(v___x_1064_);
v___x_1066_ = ((size_t)5ULL);
v___x_1067_ = lean_unsigned_to_nat(1u);
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_sub(v_depth_1055_, v___x_1068_);
v___x_1070_ = lean_usize_mul(v___x_1066_, v___x_1069_);
v_h_1071_ = lean_usize_shift_right(v_h_1065_, v___x_1070_);
v___x_1072_ = lean_nat_add(v_i_1058_, v___x_1067_);
lean_dec(v_i_1058_);
lean_inc(v_v_1063_);
lean_inc(v_k_1062_);
v___x_1073_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_entries_1059_, v_h_1071_, v_depth_1055_, v_k_1062_, v_v_1063_);
v_i_1058_ = v___x_1072_;
v_entries_1059_ = v___x_1073_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_1075_, lean_object* v_keys_1076_, lean_object* v_vals_1077_, lean_object* v_i_1078_, lean_object* v_entries_1079_){
_start:
{
size_t v_depth_boxed_1080_; lean_object* v_res_1081_; 
v_depth_boxed_1080_ = lean_unbox_usize(v_depth_1075_);
lean_dec(v_depth_1075_);
v_res_1081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_1080_, v_keys_1076_, v_vals_1077_, v_i_1078_, v_entries_1079_);
lean_dec_ref(v_vals_1077_);
lean_dec_ref(v_keys_1076_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
size_t v_x_1605__boxed_1087_; size_t v_x_1606__boxed_1088_; lean_object* v_res_1089_; 
v_x_1605__boxed_1087_ = lean_unbox_usize(v_x_1083_);
lean_dec(v_x_1083_);
v_x_1606__boxed_1088_ = lean_unbox_usize(v_x_1084_);
lean_dec(v_x_1084_);
v_res_1089_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_1082_, v_x_1605__boxed_1087_, v_x_1606__boxed_1088_, v_x_1085_, v_x_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
uint64_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
v___x_1093_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1091_);
v___x_1094_ = lean_uint64_to_usize(v___x_1093_);
v___x_1095_ = ((size_t)1ULL);
v___x_1096_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_1090_, v___x_1094_, v___x_1095_, v_x_1091_, v_x_1092_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5_spec__10(lean_object* v_vs_1097_, lean_object* v_v_1098_, lean_object* v_i_1099_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_array_get_size(v_vs_1097_);
v___x_1101_ = lean_nat_dec_lt(v_i_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_dec(v_i_1099_);
v___x_1102_ = lean_array_push(v_vs_1097_, v_v_1098_);
return v___x_1102_;
}
else
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_array_fget_borrowed(v_vs_1097_, v_i_1099_);
lean_inc(v___x_1103_);
lean_inc_ref(v_v_1098_);
v___x_1104_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(v_v_1098_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_nat_add(v_i_1099_, v___x_1105_);
lean_dec(v_i_1099_);
v_i_1099_ = v___x_1106_;
goto _start;
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_array_fset(v_vs_1097_, v_i_1099_, v_v_1098_);
lean_dec(v_i_1099_);
return v___x_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5(lean_object* v_vs_1109_, lean_object* v_v_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5_spec__10(v_vs_1109_, v_v_1110_, v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(lean_object* v_a_1113_, lean_object* v_b_1114_){
_start:
{
lean_object* v_fst_1115_; lean_object* v_fst_1116_; uint8_t v___x_1117_; 
v_fst_1115_ = lean_ctor_get(v_a_1113_, 0);
v_fst_1116_ = lean_ctor_get(v_b_1114_, 0);
v___x_1117_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1115_, v_fst_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1___boxed(lean_object* v_a_1118_, lean_object* v_b_1119_){
_start:
{
uint8_t v_res_1120_; lean_object* v_r_1121_; 
v_res_1120_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_a_1118_, v_b_1119_);
lean_dec_ref(v_b_1119_);
lean_dec_ref(v_a_1118_);
v_r_1121_ = lean_box(v_res_1120_);
return v_r_1121_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(lean_object* v_x_1122_, lean_object* v_keys_1123_, lean_object* v_v_1124_, lean_object* v_k_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_c_1129_; lean_object* v___x_1130_; 
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_x_1122_, v___x_1127_);
v_c_1129_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1123_, v_v_1124_, v___x_1128_);
lean_dec(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_k_1125_);
lean_ctor_set(v___x_1130_, 1, v_c_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v_x_1131_, lean_object* v_keys_1132_, lean_object* v_v_1133_, lean_object* v_k_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_1131_, v_keys_1132_, v_v_1133_, v_k_1134_, v_x_1135_);
lean_dec_ref(v_keys_1132_);
lean_dec(v_x_1131_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(lean_object* v_x_1141_, lean_object* v_keys_1142_, lean_object* v_v_1143_, lean_object* v_k_1144_, lean_object* v_as_1145_, lean_object* v_k_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_mid_1151_; lean_object* v_midVal_1152_; uint8_t v___x_1153_; 
v___x_1149_ = lean_nat_add(v_x_1147_, v_x_1148_);
v___x_1150_ = lean_unsigned_to_nat(1u);
v_mid_1151_ = lean_nat_shiftr(v___x_1149_, v___x_1150_);
lean_dec(v___x_1149_);
v_midVal_1152_ = lean_array_fget(v_as_1145_, v_mid_1151_);
v___x_1153_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_midVal_1152_, v_k_1146_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; 
lean_dec(v_x_1148_);
v___x_1154_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_k_1146_, v_midVal_1152_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
lean_dec(v_x_1147_);
v___x_1155_ = lean_array_get_size(v_as_1145_);
v___x_1156_ = lean_nat_dec_lt(v_mid_1151_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_dec(v_midVal_1152_);
lean_dec(v_mid_1151_);
lean_dec(v_k_1144_);
lean_dec_ref(v_v_1143_);
return v_as_1145_;
}
else
{
lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1169_; 
v_snd_1157_ = lean_ctor_get(v_midVal_1152_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_midVal_1152_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v_midVal_1152_, 0);
lean_dec(v_unused_1170_);
v___x_1159_ = v_midVal_1152_;
v_isShared_1160_ = v_isSharedCheck_1169_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_dec(v_midVal_1152_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1169_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v_xs_x27_1162_; lean_object* v___x_1163_; lean_object* v_c_1164_; lean_object* v___x_1166_; 
v___x_1161_ = lean_box(0);
v_xs_x27_1162_ = lean_array_fset(v_as_1145_, v_mid_1151_, v___x_1161_);
v___x_1163_ = lean_nat_add(v_x_1141_, v___x_1150_);
v_c_1164_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_1142_, v_v_1143_, v___x_1163_, v_snd_1157_);
lean_dec(v___x_1163_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_c_1164_);
lean_ctor_set(v___x_1159_, 0, v_k_1144_);
v___x_1166_ = v___x_1159_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_k_1144_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_c_1164_);
v___x_1166_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_array_fset(v_xs_x27_1162_, v_mid_1151_, v___x_1166_);
lean_dec(v_mid_1151_);
return v___x_1167_;
}
}
}
}
else
{
lean_dec(v_midVal_1152_);
v_x_1148_ = v_mid_1151_;
goto _start;
}
}
else
{
uint8_t v___x_1172_; 
lean_dec(v_midVal_1152_);
v___x_1172_ = lean_nat_dec_eq(v_mid_1151_, v_x_1147_);
if (v___x_1172_ == 0)
{
lean_dec(v_x_1147_);
v_x_1147_ = v_mid_1151_;
goto _start;
}
else
{
lean_object* v___x_1174_; lean_object* v_c_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_j_1178_; lean_object* v_as_1179_; lean_object* v___x_1180_; 
lean_dec(v_mid_1151_);
lean_dec(v_x_1148_);
v___x_1174_ = lean_nat_add(v_x_1141_, v___x_1150_);
v_c_1175_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1142_, v_v_1143_, v___x_1174_);
lean_dec(v___x_1174_);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_k_1144_);
lean_ctor_set(v___x_1176_, 1, v_c_1175_);
v___x_1177_ = lean_nat_add(v_x_1147_, v___x_1150_);
lean_dec(v_x_1147_);
v_j_1178_ = lean_array_get_size(v_as_1145_);
v_as_1179_ = lean_array_push(v_as_1145_, v___x_1176_);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1177_, v_as_1179_, v_j_1178_);
lean_dec(v___x_1177_);
return v___x_1180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(lean_object* v_x_1181_, lean_object* v_keys_1182_, lean_object* v_v_1183_, lean_object* v_k_1184_, lean_object* v_as_1185_, lean_object* v_k_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1187_ = lean_array_get_size(v_as_1185_);
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_nat_dec_eq(v___x_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = lean_array_fget_borrowed(v_as_1185_, v___x_1188_);
v___x_1191_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_k_1186_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint8_t v___x_1192_; 
v___x_1192_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v___x_1190_, v_k_1186_);
if (v___x_1192_ == 0)
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_nat_dec_lt(v___x_1188_, v___x_1187_);
if (v___x_1193_ == 0)
{
lean_dec(v_k_1184_);
lean_dec_ref(v_v_1183_);
return v_as_1185_;
}
else
{
lean_object* v___x_1194_; lean_object* v_xs_x27_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_inc(v___x_1190_);
v___x_1194_ = lean_box(0);
v_xs_x27_1195_ = lean_array_fset(v_as_1185_, v___x_1188_, v___x_1194_);
v___x_1196_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_1181_, v_keys_1182_, v_v_1183_, v_k_1184_, v___x_1190_);
v___x_1197_ = lean_array_fset(v_xs_x27_1195_, v___x_1188_, v___x_1196_);
return v___x_1197_;
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1198_ = lean_unsigned_to_nat(1u);
v___x_1199_ = lean_nat_sub(v___x_1187_, v___x_1198_);
v___x_1200_ = lean_array_fget_borrowed(v_as_1185_, v___x_1199_);
v___x_1201_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v___x_1200_, v_k_1186_);
if (v___x_1201_ == 0)
{
uint8_t v___x_1202_; 
v___x_1202_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_k_1186_, v___x_1200_);
if (v___x_1202_ == 0)
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_nat_dec_lt(v___x_1199_, v___x_1187_);
if (v___x_1203_ == 0)
{
lean_dec(v___x_1199_);
lean_dec(v_k_1184_);
lean_dec_ref(v_v_1183_);
return v_as_1185_;
}
else
{
lean_object* v___x_1204_; lean_object* v_xs_x27_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_inc(v___x_1200_);
v___x_1204_ = lean_box(0);
v_xs_x27_1205_ = lean_array_fset(v_as_1185_, v___x_1199_, v___x_1204_);
v___x_1206_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_1181_, v_keys_1182_, v_v_1183_, v_k_1184_, v___x_1200_);
v___x_1207_ = lean_array_fset(v_xs_x27_1205_, v___x_1199_, v___x_1206_);
lean_dec(v___x_1199_);
return v___x_1207_;
}
}
else
{
lean_object* v___x_1208_; 
v___x_1208_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1181_, v_keys_1182_, v_v_1183_, v_k_1184_, v_as_1185_, v_k_1186_, v___x_1188_, v___x_1199_);
return v___x_1208_;
}
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec(v___x_1199_);
v___x_1209_ = lean_box(0);
v___x_1210_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_1181_, v_keys_1182_, v_v_1183_, v_k_1184_, v___x_1209_);
v___x_1211_ = lean_array_push(v_as_1185_, v___x_1210_);
return v___x_1211_;
}
}
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_as_1214_; lean_object* v___x_1215_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_1181_, v_keys_1182_, v_v_1183_, v_k_1184_, v___x_1212_);
v_as_1214_ = lean_array_push(v_as_1185_, v___x_1213_);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1188_, v_as_1214_, v___x_1187_);
return v___x_1215_;
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_1181_, v_keys_1182_, v_v_1183_, v_k_1184_, v___x_1216_);
v___x_1218_ = lean_array_push(v_as_1185_, v___x_1217_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(lean_object* v_keys_1219_, lean_object* v_v_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
lean_object* v_vs_1223_; lean_object* v_children_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1241_; 
v_vs_1223_ = lean_ctor_get(v_x_1222_, 0);
v_children_1224_ = lean_ctor_get(v_x_1222_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_x_1222_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1226_ = v_x_1222_;
v_isShared_1227_ = v_isSharedCheck_1241_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_children_1224_);
lean_inc(v_vs_1223_);
lean_dec(v_x_1222_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1241_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_array_get_size(v_keys_1219_);
v___x_1229_ = lean_nat_dec_lt(v_x_1221_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1230_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5(v_vs_1223_, v_v_1220_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1230_);
v___x_1232_ = v___x_1226_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_children_1224_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
else
{
lean_object* v_k_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_c_1237_; lean_object* v___x_1239_; 
v_k_1234_ = lean_array_fget_borrowed(v_keys_1219_, v_x_1221_);
v___x_1235_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1));
lean_inc_n(v_k_1234_, 2);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_k_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v_c_1237_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(v_x_1221_, v_keys_1219_, v_v_1220_, v_k_1234_, v_children_1224_, v___x_1236_);
lean_dec_ref(v___x_1236_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v_c_1237_);
v___x_1239_ = v___x_1226_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_vs_1223_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_c_1237_);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(lean_object* v_x_1242_, lean_object* v_keys_1243_, lean_object* v_v_1244_, lean_object* v_k_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v_snd_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1257_; 
v_snd_1247_ = lean_ctor_get(v_x_1246_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_x_1246_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v_x_1246_, 0);
lean_dec(v_unused_1258_);
v___x_1249_ = v_x_1246_;
v_isShared_1250_ = v_isSharedCheck_1257_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_snd_1247_);
lean_dec(v_x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1257_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_c_1253_; lean_object* v___x_1255_; 
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_nat_add(v_x_1242_, v___x_1251_);
v_c_1253_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_1243_, v_v_1244_, v___x_1252_, v_snd_1247_);
lean_dec(v___x_1252_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v_c_1253_);
lean_ctor_set(v___x_1249_, 0, v_k_1245_);
v___x_1255_ = v___x_1249_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_c_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2___boxed(lean_object* v_x_1259_, lean_object* v_keys_1260_, lean_object* v_v_1261_, lean_object* v_k_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_1259_, v_keys_1260_, v_v_1261_, v_k_1262_, v_x_1263_);
lean_dec_ref(v_keys_1260_);
lean_dec(v_x_1259_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___boxed(lean_object* v_keys_1265_, lean_object* v_v_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_1265_, v_v_1266_, v_x_1267_, v_x_1268_);
lean_dec(v_x_1267_);
lean_dec_ref(v_keys_1265_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_x_1270_, lean_object* v_keys_1271_, lean_object* v_v_1272_, lean_object* v_k_1273_, lean_object* v_as_1274_, lean_object* v_k_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1270_, v_keys_1271_, v_v_1272_, v_k_1273_, v_as_1274_, v_k_1275_, v_x_1276_, v_x_1277_);
lean_dec_ref(v_k_1275_);
lean_dec_ref(v_keys_1271_);
lean_dec(v_x_1270_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___boxed(lean_object* v_x_1279_, lean_object* v_keys_1280_, lean_object* v_v_1281_, lean_object* v_k_1282_, lean_object* v_as_1283_, lean_object* v_k_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(v_x_1279_, v_keys_1280_, v_v_1281_, v_k_1282_, v_as_1283_, v_k_1284_);
lean_dec_ref(v_k_1284_);
lean_dec_ref(v_keys_1280_);
lean_dec(v_x_1279_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_1286_, lean_object* v_vals_1287_, lean_object* v_i_1288_, lean_object* v_k_1289_){
_start:
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = lean_array_get_size(v_keys_1286_);
v___x_1291_ = lean_nat_dec_lt(v_i_1288_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
lean_dec(v_i_1288_);
v___x_1292_ = lean_box(0);
return v___x_1292_;
}
else
{
lean_object* v_k_x27_1293_; uint8_t v___x_1294_; 
v_k_x27_1293_ = lean_array_fget_borrowed(v_keys_1286_, v_i_1288_);
v___x_1294_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1289_, v_k_x27_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_nat_add(v_i_1288_, v___x_1295_);
lean_dec(v_i_1288_);
v_i_1288_ = v___x_1296_;
goto _start;
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_array_fget_borrowed(v_vals_1287_, v_i_1288_);
lean_dec(v_i_1288_);
lean_inc(v___x_1298_);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_1300_, lean_object* v_vals_1301_, lean_object* v_i_1302_, lean_object* v_k_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1300_, v_vals_1301_, v_i_1302_, v_k_1303_);
lean_dec(v_k_1303_);
lean_dec_ref(v_vals_1301_);
lean_dec_ref(v_keys_1300_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1305_, size_t v_x_1306_, lean_object* v_x_1307_){
_start:
{
if (lean_obj_tag(v_x_1305_) == 0)
{
lean_object* v_es_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1329_; 
v_es_1308_ = lean_ctor_get(v_x_1305_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_x_1305_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1310_ = v_x_1305_;
v_isShared_1311_ = v_isSharedCheck_1329_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_es_1308_);
lean_dec(v_x_1305_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1329_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; size_t v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; lean_object* v_j_1316_; lean_object* v___x_1317_; 
v___x_1312_ = lean_box(2);
v___x_1313_ = ((size_t)5ULL);
v___x_1314_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1315_ = lean_usize_land(v_x_1306_, v___x_1314_);
v_j_1316_ = lean_usize_to_nat(v___x_1315_);
v___x_1317_ = lean_array_get(v___x_1312_, v_es_1308_, v_j_1316_);
lean_dec(v_j_1316_);
lean_dec_ref(v_es_1308_);
switch(lean_obj_tag(v___x_1317_))
{
case 0:
{
lean_object* v_key_1318_; lean_object* v_val_1319_; uint8_t v___x_1320_; 
v_key_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_key_1318_);
v_val_1319_ = lean_ctor_get(v___x_1317_, 1);
lean_inc(v_val_1319_);
lean_dec_ref(v___x_1317_);
v___x_1320_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1307_, v_key_1318_);
lean_dec(v_key_1318_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
lean_dec(v_val_1319_);
lean_del_object(v___x_1310_);
v___x_1321_ = lean_box(0);
return v___x_1321_;
}
else
{
lean_object* v___x_1323_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 1);
lean_ctor_set(v___x_1310_, 0, v_val_1319_);
v___x_1323_ = v___x_1310_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_val_1319_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
case 1:
{
lean_object* v_node_1325_; size_t v___x_1326_; 
lean_del_object(v___x_1310_);
v_node_1325_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_node_1325_);
lean_dec_ref(v___x_1317_);
v___x_1326_ = lean_usize_shift_right(v_x_1306_, v___x_1313_);
v_x_1305_ = v_node_1325_;
v_x_1306_ = v___x_1326_;
goto _start;
}
default: 
{
lean_object* v___x_1328_; 
lean_del_object(v___x_1310_);
v___x_1328_ = lean_box(0);
return v___x_1328_;
}
}
}
}
else
{
lean_object* v_ks_1330_; lean_object* v_vs_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_ks_1330_ = lean_ctor_get(v_x_1305_, 0);
lean_inc_ref(v_ks_1330_);
v_vs_1331_ = lean_ctor_get(v_x_1305_, 1);
lean_inc_ref(v_vs_1331_);
lean_dec_ref(v_x_1305_);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_1330_, v_vs_1331_, v___x_1332_, v_x_1307_);
lean_dec_ref(v_vs_1331_);
lean_dec_ref(v_ks_1330_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
size_t v_x_2045__boxed_1337_; lean_object* v_res_1338_; 
v_x_2045__boxed_1337_ = lean_unbox_usize(v_x_1335_);
lean_dec(v_x_1335_);
v_res_1338_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_1334_, v_x_2045__boxed_1337_, v_x_1336_);
lean_dec(v_x_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
uint64_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1340_);
v___x_1342_ = lean_uint64_to_usize(v___x_1341_);
v___x_1343_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_1339_, v___x_1342_, v_x_1340_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_x_1344_, v_x_1345_);
lean_dec(v_x_1345_);
return v_res_1346_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3(lean_object* v_msg_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0);
v___x_1350_ = lean_panic_fn_borrowed(v___x_1349_, v_msg_1348_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1354_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2));
v___x_1355_ = lean_unsigned_to_nat(23u);
v___x_1356_ = lean_unsigned_to_nat(166u);
v___x_1357_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1));
v___x_1358_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0));
v___x_1359_ = l_mkPanicMessageWithDecl(v___x_1358_, v___x_1357_, v___x_1356_, v___x_1355_, v___x_1354_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(lean_object* v_d_1360_, lean_object* v_keys_1361_, lean_object* v_v_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1363_ = lean_array_get_size(v_keys_1361_);
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_nat_dec_eq(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v_k_1367_; lean_object* v___x_1368_; 
v___x_1366_ = lean_box(0);
v_k_1367_ = lean_array_get_borrowed(v___x_1366_, v_keys_1361_, v___x_1364_);
lean_inc_ref(v_d_1360_);
v___x_1368_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_d_1360_, v_k_1367_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; lean_object* v_c_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_unsigned_to_nat(1u);
v_c_1370_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1361_, v_v_1362_, v___x_1369_);
lean_inc(v_k_1367_);
v___x_1371_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_d_1360_, v_k_1367_, v_c_1370_);
return v___x_1371_;
}
else
{
lean_object* v_val_1372_; lean_object* v___x_1373_; lean_object* v_c_1374_; lean_object* v___x_1375_; 
v_val_1372_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_val_1372_);
lean_dec_ref(v___x_1368_);
v___x_1373_ = lean_unsigned_to_nat(1u);
v_c_1374_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_1361_, v_v_1362_, v___x_1373_, v_val_1372_);
lean_inc(v_k_1367_);
v___x_1375_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_d_1360_, v_k_1367_, v_c_1374_);
return v___x_1375_;
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref(v_v_1362_);
lean_dec_ref(v_d_1360_);
v___x_1376_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3);
v___x_1377_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3(v___x_1376_);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___boxed(lean_object* v_d_1378_, lean_object* v_keys_1379_, lean_object* v_v_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(v_d_1378_, v_keys_1379_, v_v_1380_);
lean_dec_ref(v_keys_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(lean_object* v_d_1382_, lean_object* v_e_1383_){
_start:
{
lean_object* v_specs_1384_; lean_object* v_erased_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1394_; 
v_specs_1384_ = lean_ctor_get(v_d_1382_, 0);
v_erased_1385_ = lean_ctor_get(v_d_1382_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_d_1382_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1387_ = v_d_1382_;
v_isShared_1388_ = v_isSharedCheck_1394_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_erased_1385_);
lean_inc(v_specs_1384_);
lean_dec(v_d_1382_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1394_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v_keys_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v_keys_1389_ = lean_ctor_get(v_e_1383_, 0);
lean_inc_ref(v_keys_1389_);
v___x_1390_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(v_specs_1384_, v_keys_1389_, v_e_1383_);
lean_dec_ref(v_keys_1389_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1390_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_erased_1385_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(lean_object* v_00_u03b2_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_x_1396_, v_x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(v_00_u03b2_1399_, v_x_1400_, v_x_1401_);
lean_dec(v_x_1401_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1(lean_object* v_00_u03b2_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_x_1404_, v_x_1405_, v_x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1408_, lean_object* v_x_1409_, size_t v_x_1410_, lean_object* v_x_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_1409_, v_x_1410_, v_x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_, lean_object* v_x_1416_){
_start:
{
size_t v_x_2208__boxed_1417_; lean_object* v_res_1418_; 
v_x_2208__boxed_1417_ = lean_unbox_usize(v_x_1415_);
lean_dec(v_x_1415_);
v_res_1418_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(v_00_u03b2_1413_, v_x_1414_, v_x_2208__boxed_1417_, v_x_1416_);
lean_dec(v_x_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1419_, lean_object* v_x_1420_, size_t v_x_1421_, size_t v_x_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_1420_, v_x_1421_, v_x_1422_, v_x_1423_, v_x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
size_t v_x_2219__boxed_1432_; size_t v_x_2220__boxed_1433_; lean_object* v_res_1434_; 
v_x_2219__boxed_1432_ = lean_unbox_usize(v_x_1428_);
lean_dec(v_x_1428_);
v_x_2220__boxed_1433_ = lean_unbox_usize(v_x_1429_);
lean_dec(v_x_1429_);
v_res_1434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3(v_00_u03b2_1426_, v_x_1427_, v_x_2219__boxed_1432_, v_x_2220__boxed_1433_, v_x_1430_, v_x_1431_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1435_, lean_object* v_keys_1436_, lean_object* v_vals_1437_, lean_object* v_heq_1438_, lean_object* v_i_1439_, lean_object* v_k_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1436_, v_vals_1437_, v_i_1439_, v_k_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1442_, lean_object* v_keys_1443_, lean_object* v_vals_1444_, lean_object* v_heq_1445_, lean_object* v_i_1446_, lean_object* v_k_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1442_, v_keys_1443_, v_vals_1444_, v_heq_1445_, v_i_1446_, v_k_1447_);
lean_dec(v_k_1447_);
lean_dec_ref(v_vals_1444_);
lean_dec_ref(v_keys_1443_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1449_, lean_object* v_n_1450_, lean_object* v_k_1451_, lean_object* v_v_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(v_n_1450_, v_k_1451_, v_v_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_1454_, size_t v_depth_1455_, lean_object* v_keys_1456_, lean_object* v_vals_1457_, lean_object* v_heq_1458_, lean_object* v_i_1459_, lean_object* v_entries_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_1455_, v_keys_1456_, v_vals_1457_, v_i_1459_, v_entries_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1462_, lean_object* v_depth_1463_, lean_object* v_keys_1464_, lean_object* v_vals_1465_, lean_object* v_heq_1466_, lean_object* v_i_1467_, lean_object* v_entries_1468_){
_start:
{
size_t v_depth_boxed_1469_; lean_object* v_res_1470_; 
v_depth_boxed_1469_ = lean_unbox_usize(v_depth_1463_);
lean_dec(v_depth_1463_);
v_res_1470_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_1462_, v_depth_boxed_1469_, v_keys_1464_, v_vals_1465_, v_heq_1466_, v_i_1467_, v_entries_1468_);
lean_dec_ref(v_vals_1465_);
lean_dec_ref(v_keys_1464_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12(lean_object* v_x_1471_, lean_object* v_keys_1472_, lean_object* v_v_1473_, lean_object* v_k_1474_, lean_object* v_as_1475_, lean_object* v_k_1476_, lean_object* v_x_1477_, lean_object* v_x_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_1471_, v_keys_1472_, v_v_1473_, v_k_1474_, v_as_1475_, v_k_1476_, v_x_1477_, v_x_1478_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_x_1482_, lean_object* v_keys_1483_, lean_object* v_v_1484_, lean_object* v_k_1485_, lean_object* v_as_1486_, lean_object* v_k_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12(v_x_1482_, v_keys_1483_, v_v_1484_, v_k_1485_, v_as_1486_, v_k_1487_, v_x_1488_, v_x_1489_, v_x_1490_, v_x_1491_);
lean_dec_ref(v_k_1487_);
lean_dec_ref(v_keys_1483_);
lean_dec(v_x_1482_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_1494_, v_x_1495_, v_x_1496_, v_x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1499_, lean_object* v_i_1500_, lean_object* v_k_1501_){
_start:
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = lean_array_get_size(v_keys_1499_);
v___x_1503_ = lean_nat_dec_lt(v_i_1500_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_dec_ref(v_k_1501_);
lean_dec(v_i_1500_);
return v___x_1503_;
}
else
{
lean_object* v_k_x27_1504_; uint8_t v___x_1505_; 
v_k_x27_1504_ = lean_array_fget_borrowed(v_keys_1499_, v_i_1500_);
lean_inc(v_k_x27_1504_);
lean_inc_ref(v_k_1501_);
v___x_1505_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_k_1501_, v_k_x27_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_unsigned_to_nat(1u);
v___x_1507_ = lean_nat_add(v_i_1500_, v___x_1506_);
lean_dec(v_i_1500_);
v_i_1500_ = v___x_1507_;
goto _start;
}
else
{
lean_dec_ref(v_k_1501_);
lean_dec(v_i_1500_);
return v___x_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1509_, lean_object* v_i_1510_, lean_object* v_k_1511_){
_start:
{
uint8_t v_res_1512_; lean_object* v_r_1513_; 
v_res_1512_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_1509_, v_i_1510_, v_k_1511_);
lean_dec_ref(v_keys_1509_);
v_r_1513_ = lean_box(v_res_1512_);
return v_r_1513_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(lean_object* v_x_1514_, size_t v_x_1515_, lean_object* v_x_1516_){
_start:
{
if (lean_obj_tag(v_x_1514_) == 0)
{
lean_object* v_es_1517_; lean_object* v___x_1518_; size_t v___x_1519_; size_t v___x_1520_; size_t v___x_1521_; lean_object* v_j_1522_; lean_object* v___x_1523_; 
v_es_1517_ = lean_ctor_get(v_x_1514_, 0);
lean_inc_ref(v_es_1517_);
lean_dec_ref(v_x_1514_);
v___x_1518_ = lean_box(2);
v___x_1519_ = ((size_t)5ULL);
v___x_1520_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1521_ = lean_usize_land(v_x_1515_, v___x_1520_);
v_j_1522_ = lean_usize_to_nat(v___x_1521_);
v___x_1523_ = lean_array_get(v___x_1518_, v_es_1517_, v_j_1522_);
lean_dec(v_j_1522_);
lean_dec_ref(v_es_1517_);
switch(lean_obj_tag(v___x_1523_))
{
case 0:
{
lean_object* v_key_1524_; uint8_t v___x_1525_; 
v_key_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_key_1524_);
lean_dec_ref(v___x_1523_);
v___x_1525_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1516_, v_key_1524_);
return v___x_1525_;
}
case 1:
{
lean_object* v_node_1526_; size_t v___x_1527_; 
v_node_1526_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_node_1526_);
lean_dec_ref(v___x_1523_);
v___x_1527_ = lean_usize_shift_right(v_x_1515_, v___x_1519_);
v_x_1514_ = v_node_1526_;
v_x_1515_ = v___x_1527_;
goto _start;
}
default: 
{
uint8_t v___x_1529_; 
lean_dec_ref(v_x_1516_);
v___x_1529_ = 0;
return v___x_1529_;
}
}
}
else
{
lean_object* v_ks_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_ks_1530_ = lean_ctor_get(v_x_1514_, 0);
lean_inc_ref(v_ks_1530_);
lean_dec_ref(v_x_1514_);
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_ks_1530_, v___x_1531_, v_x_1516_);
lean_dec_ref(v_ks_1530_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg___boxed(lean_object* v_x_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_){
_start:
{
size_t v_x_146__boxed_1536_; uint8_t v_res_1537_; lean_object* v_r_1538_; 
v_x_146__boxed_1536_ = lean_unbox_usize(v_x_1534_);
lean_dec(v_x_1534_);
v_res_1537_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_1533_, v_x_146__boxed_1536_, v_x_1535_);
v_r_1538_ = lean_box(v_res_1537_);
return v_r_1538_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(lean_object* v_x_1539_, lean_object* v_x_1540_){
_start:
{
uint64_t v___y_1542_; lean_object* v___y_1546_; lean_object* v_declName_1549_; 
v_declName_1549_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_declName_1549_);
v___y_1546_ = v_declName_1549_;
goto v___jp_1545_;
v___jp_1541_:
{
size_t v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = lean_uint64_to_usize(v___y_1542_);
v___x_1544_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_1539_, v___x_1543_, v_x_1540_);
return v___x_1544_;
}
v___jp_1545_:
{
if (lean_obj_tag(v___y_1546_) == 0)
{
uint64_t v___x_1547_; 
v___x_1547_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_1542_ = v___x_1547_;
goto v___jp_1541_;
}
else
{
uint64_t v_hash_1548_; 
v_hash_1548_ = lean_ctor_get_uint64(v___y_1546_, sizeof(void*)*2);
lean_dec(v___y_1546_);
v___y_1542_ = v_hash_1548_;
goto v___jp_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg___boxed(lean_object* v_x_1550_, lean_object* v_x_1551_){
_start:
{
uint8_t v_res_1552_; lean_object* v_r_1553_; 
v_res_1552_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_1550_, v_x_1551_);
v_r_1553_ = lean_box(v_res_1552_);
return v_r_1553_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(lean_object* v_d_1554_, lean_object* v_thmId_1555_){
_start:
{
lean_object* v_erased_1556_; uint8_t v___x_1557_; 
v_erased_1556_ = lean_ctor_get(v_d_1554_, 1);
lean_inc_ref(v_erased_1556_);
lean_dec_ref(v_d_1554_);
v___x_1557_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_erased_1556_, v_thmId_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased___boxed(lean_object* v_d_1558_, lean_object* v_thmId_1559_){
_start:
{
uint8_t v_res_1560_; lean_object* v_r_1561_; 
v_res_1560_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_d_1558_, v_thmId_1559_);
v_r_1561_ = lean_box(v_res_1560_);
return v_r_1561_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(lean_object* v_00_u03b2_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_){
_start:
{
uint8_t v___x_1565_; 
v___x_1565_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_1563_, v_x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___boxed(lean_object* v_00_u03b2_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_){
_start:
{
uint8_t v_res_1569_; lean_object* v_r_1570_; 
v_res_1569_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(v_00_u03b2_1566_, v_x_1567_, v_x_1568_);
v_r_1570_ = lean_box(v_res_1569_);
return v_r_1570_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(lean_object* v_00_u03b2_1571_, lean_object* v_x_1572_, size_t v_x_1573_, lean_object* v_x_1574_){
_start:
{
uint8_t v___x_1575_; 
v___x_1575_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_1572_, v_x_1573_, v_x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1576_, lean_object* v_x_1577_, lean_object* v_x_1578_, lean_object* v_x_1579_){
_start:
{
size_t v_x_228__boxed_1580_; uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_x_228__boxed_1580_ = lean_unbox_usize(v_x_1578_);
lean_dec(v_x_1578_);
v_res_1581_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(v_00_u03b2_1576_, v_x_1577_, v_x_228__boxed_1580_, v_x_1579_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1583_, lean_object* v_keys_1584_, lean_object* v_vals_1585_, lean_object* v_heq_1586_, lean_object* v_i_1587_, lean_object* v_k_1588_){
_start:
{
uint8_t v___x_1589_; 
v___x_1589_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_1584_, v_i_1587_, v_k_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1590_, lean_object* v_keys_1591_, lean_object* v_vals_1592_, lean_object* v_heq_1593_, lean_object* v_i_1594_, lean_object* v_k_1595_){
_start:
{
uint8_t v_res_1596_; lean_object* v_r_1597_; 
v_res_1596_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(v_00_u03b2_1590_, v_keys_1591_, v_vals_1592_, v_heq_1593_, v_i_1594_, v_k_1595_);
lean_dec_ref(v_vals_1592_);
lean_dec_ref(v_keys_1591_);
v_r_1597_ = lean_box(v_res_1596_);
return v_r_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1598_, lean_object* v_x_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_){
_start:
{
lean_object* v_ks_1602_; lean_object* v_vs_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1627_; 
v_ks_1602_ = lean_ctor_get(v_x_1598_, 0);
v_vs_1603_ = lean_ctor_get(v_x_1598_, 1);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_x_1598_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1605_ = v_x_1598_;
v_isShared_1606_ = v_isSharedCheck_1627_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_vs_1603_);
lean_inc(v_ks_1602_);
lean_dec(v_x_1598_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1627_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = lean_array_get_size(v_ks_1602_);
v___x_1608_ = lean_nat_dec_lt(v_x_1599_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
lean_dec(v_x_1599_);
v___x_1609_ = lean_array_push(v_ks_1602_, v_x_1600_);
v___x_1610_ = lean_array_push(v_vs_1603_, v_x_1601_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 1, v___x_1610_);
lean_ctor_set(v___x_1605_, 0, v___x_1609_);
v___x_1612_ = v___x_1605_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
else
{
lean_object* v_k_x27_1614_; uint8_t v___x_1615_; 
v_k_x27_1614_ = lean_array_fget_borrowed(v_ks_1602_, v_x_1599_);
lean_inc(v_k_x27_1614_);
lean_inc_ref(v_x_1600_);
v___x_1615_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1600_, v_k_x27_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1617_; 
if (v_isShared_1606_ == 0)
{
v___x_1617_ = v___x_1605_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_ks_1602_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_vs_1603_);
v___x_1617_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_unsigned_to_nat(1u);
v___x_1619_ = lean_nat_add(v_x_1599_, v___x_1618_);
lean_dec(v_x_1599_);
v_x_1598_ = v___x_1617_;
v_x_1599_ = v___x_1619_;
goto _start;
}
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1622_ = lean_array_fset(v_ks_1602_, v_x_1599_, v_x_1600_);
v___x_1623_ = lean_array_fset(v_vs_1603_, v_x_1599_, v_x_1601_);
lean_dec(v_x_1599_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 1, v___x_1623_);
lean_ctor_set(v___x_1605_, 0, v___x_1622_);
v___x_1625_ = v___x_1605_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v___x_1623_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1628_, lean_object* v_k_1629_, lean_object* v_v_1630_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1628_, v___x_1631_, v_k_1629_, v_v_1630_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(lean_object* v_x_1634_, size_t v_x_1635_, size_t v_x_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_){
_start:
{
if (lean_obj_tag(v_x_1634_) == 0)
{
lean_object* v_es_1639_; size_t v___x_1640_; size_t v___x_1641_; size_t v___x_1642_; size_t v___x_1643_; lean_object* v_j_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v_es_1639_ = lean_ctor_get(v_x_1634_, 0);
v___x_1640_ = ((size_t)5ULL);
v___x_1641_ = ((size_t)1ULL);
v___x_1642_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1643_ = lean_usize_land(v_x_1635_, v___x_1642_);
v_j_1644_ = lean_usize_to_nat(v___x_1643_);
v___x_1645_ = lean_array_get_size(v_es_1639_);
v___x_1646_ = lean_nat_dec_lt(v_j_1644_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_dec(v_j_1644_);
lean_dec(v_x_1638_);
lean_dec_ref(v_x_1637_);
return v_x_1634_;
}
else
{
lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1683_; 
lean_inc_ref(v_es_1639_);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1683_ == 0)
{
lean_object* v_unused_1684_; 
v_unused_1684_ = lean_ctor_get(v_x_1634_, 0);
lean_dec(v_unused_1684_);
v___x_1648_ = v_x_1634_;
v_isShared_1649_ = v_isSharedCheck_1683_;
goto v_resetjp_1647_;
}
else
{
lean_dec(v_x_1634_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1683_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v_v_1650_; lean_object* v___x_1651_; lean_object* v_xs_x27_1652_; lean_object* v___y_1654_; 
v_v_1650_ = lean_array_fget(v_es_1639_, v_j_1644_);
v___x_1651_ = lean_box(0);
v_xs_x27_1652_ = lean_array_fset(v_es_1639_, v_j_1644_, v___x_1651_);
switch(lean_obj_tag(v_v_1650_))
{
case 0:
{
lean_object* v_key_1659_; lean_object* v_val_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1670_; 
v_key_1659_ = lean_ctor_get(v_v_1650_, 0);
v_val_1660_ = lean_ctor_get(v_v_1650_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_v_1650_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1662_ = v_v_1650_;
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_val_1660_);
lean_inc(v_key_1659_);
lean_dec(v_v_1650_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
uint8_t v___x_1664_; 
lean_inc(v_key_1659_);
lean_inc_ref(v_x_1637_);
v___x_1664_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1637_, v_key_1659_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_del_object(v___x_1662_);
v___x_1665_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1659_, v_val_1660_, v_x_1637_, v_x_1638_);
v___x_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
v___y_1654_ = v___x_1666_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1668_; 
lean_dec(v_val_1660_);
lean_dec(v_key_1659_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v_x_1638_);
lean_ctor_set(v___x_1662_, 0, v_x_1637_);
v___x_1668_ = v___x_1662_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_x_1637_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_x_1638_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
v___y_1654_ = v___x_1668_;
goto v___jp_1653_;
}
}
}
}
case 1:
{
lean_object* v_node_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1681_; 
v_node_1671_ = lean_ctor_get(v_v_1650_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_v_1650_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1673_ = v_v_1650_;
v_isShared_1674_ = v_isSharedCheck_1681_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_node_1671_);
lean_dec(v_v_1650_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1681_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
size_t v___x_1675_; size_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1675_ = lean_usize_shift_right(v_x_1635_, v___x_1640_);
v___x_1676_ = lean_usize_add(v_x_1636_, v___x_1641_);
v___x_1677_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_node_1671_, v___x_1675_, v___x_1676_, v_x_1637_, v_x_1638_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1677_);
v___x_1679_ = v___x_1673_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
v___y_1654_ = v___x_1679_;
goto v___jp_1653_;
}
}
}
default: 
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_x_1637_);
lean_ctor_set(v___x_1682_, 1, v_x_1638_);
v___y_1654_ = v___x_1682_;
goto v___jp_1653_;
}
}
v___jp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_array_fset(v_xs_x27_1652_, v_j_1644_, v___y_1654_);
lean_dec(v_j_1644_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1655_);
v___x_1657_ = v___x_1648_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
else
{
lean_object* v_ks_1685_; lean_object* v_vs_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1706_; 
v_ks_1685_ = lean_ctor_get(v_x_1634_, 0);
v_vs_1686_ = lean_ctor_get(v_x_1634_, 1);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1688_ = v_x_1634_;
v_isShared_1689_ = v_isSharedCheck_1706_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_vs_1686_);
lean_inc(v_ks_1685_);
lean_dec(v_x_1634_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1706_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_ks_1685_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_vs_1686_);
v___x_1691_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v_newNode_1692_; uint8_t v___y_1694_; size_t v___x_1700_; uint8_t v___x_1701_; 
v_newNode_1692_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v___x_1691_, v_x_1637_, v_x_1638_);
v___x_1700_ = ((size_t)7ULL);
v___x_1701_ = lean_usize_dec_le(v___x_1700_, v_x_1636_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1702_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1692_);
v___x_1703_ = lean_unsigned_to_nat(4u);
v___x_1704_ = lean_nat_dec_lt(v___x_1702_, v___x_1703_);
lean_dec(v___x_1702_);
v___y_1694_ = v___x_1704_;
goto v___jp_1693_;
}
else
{
v___y_1694_ = v___x_1701_;
goto v___jp_1693_;
}
v___jp_1693_:
{
if (v___y_1694_ == 0)
{
lean_object* v_ks_1695_; lean_object* v_vs_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_ks_1695_ = lean_ctor_get(v_newNode_1692_, 0);
lean_inc_ref(v_ks_1695_);
v_vs_1696_ = lean_ctor_get(v_newNode_1692_, 1);
lean_inc_ref(v_vs_1696_);
lean_dec_ref(v_newNode_1692_);
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0);
v___x_1699_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_x_1636_, v_ks_1695_, v_vs_1696_, v___x_1697_, v___x_1698_);
lean_dec_ref(v_vs_1696_);
lean_dec_ref(v_ks_1695_);
return v___x_1699_;
}
else
{
return v_newNode_1692_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(size_t v_depth_1707_, lean_object* v_keys_1708_, lean_object* v_vals_1709_, lean_object* v_i_1710_, lean_object* v_entries_1711_){
_start:
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = lean_array_get_size(v_keys_1708_);
v___x_1713_ = lean_nat_dec_lt(v_i_1710_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_dec(v_i_1710_);
return v_entries_1711_;
}
else
{
lean_object* v_k_1714_; lean_object* v_v_1715_; uint64_t v___y_1717_; lean_object* v___y_1729_; lean_object* v_declName_1732_; 
v_k_1714_ = lean_array_fget_borrowed(v_keys_1708_, v_i_1710_);
v_v_1715_ = lean_array_fget_borrowed(v_vals_1709_, v_i_1710_);
v_declName_1732_ = lean_ctor_get(v_k_1714_, 0);
lean_inc(v_declName_1732_);
v___y_1729_ = v_declName_1732_;
goto v___jp_1728_;
v___jp_1716_:
{
size_t v_h_1718_; size_t v___x_1719_; lean_object* v___x_1720_; size_t v___x_1721_; size_t v___x_1722_; size_t v___x_1723_; size_t v_h_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_h_1718_ = lean_uint64_to_usize(v___y_1717_);
v___x_1719_ = ((size_t)5ULL);
v___x_1720_ = lean_unsigned_to_nat(1u);
v___x_1721_ = ((size_t)1ULL);
v___x_1722_ = lean_usize_sub(v_depth_1707_, v___x_1721_);
v___x_1723_ = lean_usize_mul(v___x_1719_, v___x_1722_);
v_h_1724_ = lean_usize_shift_right(v_h_1718_, v___x_1723_);
v___x_1725_ = lean_nat_add(v_i_1710_, v___x_1720_);
lean_dec(v_i_1710_);
lean_inc(v_v_1715_);
lean_inc(v_k_1714_);
v___x_1726_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_entries_1711_, v_h_1724_, v_depth_1707_, v_k_1714_, v_v_1715_);
v_i_1710_ = v___x_1725_;
v_entries_1711_ = v___x_1726_;
goto _start;
}
v___jp_1728_:
{
if (lean_obj_tag(v___y_1729_) == 0)
{
uint64_t v___x_1730_; 
v___x_1730_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_1717_ = v___x_1730_;
goto v___jp_1716_;
}
else
{
uint64_t v_hash_1731_; 
v_hash_1731_ = lean_ctor_get_uint64(v___y_1729_, sizeof(void*)*2);
lean_dec(v___y_1729_);
v___y_1717_ = v_hash_1731_;
goto v___jp_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1733_, lean_object* v_keys_1734_, lean_object* v_vals_1735_, lean_object* v_i_1736_, lean_object* v_entries_1737_){
_start:
{
size_t v_depth_boxed_1738_; lean_object* v_res_1739_; 
v_depth_boxed_1738_ = lean_unbox_usize(v_depth_1733_);
lean_dec(v_depth_1733_);
v_res_1739_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1738_, v_keys_1734_, v_vals_1735_, v_i_1736_, v_entries_1737_);
lean_dec_ref(v_vals_1735_);
lean_dec_ref(v_keys_1734_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_){
_start:
{
size_t v_x_400__boxed_1745_; size_t v_x_401__boxed_1746_; lean_object* v_res_1747_; 
v_x_400__boxed_1745_ = lean_unbox_usize(v_x_1741_);
lean_dec(v_x_1741_);
v_x_401__boxed_1746_ = lean_unbox_usize(v_x_1742_);
lean_dec(v_x_1742_);
v_res_1747_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_1740_, v_x_400__boxed_1745_, v_x_401__boxed_1746_, v_x_1743_, v_x_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(lean_object* v_x_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_){
_start:
{
uint64_t v___y_1752_; lean_object* v___y_1757_; lean_object* v_declName_1760_; 
v_declName_1760_ = lean_ctor_get(v_x_1749_, 0);
lean_inc(v_declName_1760_);
v___y_1757_ = v_declName_1760_;
goto v___jp_1756_;
v___jp_1751_:
{
size_t v___x_1753_; size_t v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_uint64_to_usize(v___y_1752_);
v___x_1754_ = ((size_t)1ULL);
v___x_1755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_1748_, v___x_1753_, v___x_1754_, v_x_1749_, v_x_1750_);
return v___x_1755_;
}
v___jp_1756_:
{
if (lean_obj_tag(v___y_1757_) == 0)
{
uint64_t v___x_1758_; 
v___x_1758_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_1752_ = v___x_1758_;
goto v___jp_1751_;
}
else
{
uint64_t v_hash_1759_; 
v_hash_1759_ = lean_ctor_get_uint64(v___y_1757_, sizeof(void*)*2);
lean_dec(v___y_1757_);
v___y_1752_ = v_hash_1759_;
goto v___jp_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(lean_object* v_d_1761_, lean_object* v_thmId_1762_){
_start:
{
lean_object* v_specs_1763_; lean_object* v_erased_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1773_; 
v_specs_1763_ = lean_ctor_get(v_d_1761_, 0);
v_erased_1764_ = lean_ctor_get(v_d_1761_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_d_1761_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1766_ = v_d_1761_;
v_isShared_1767_ = v_isSharedCheck_1773_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_erased_1764_);
lean_inc(v_specs_1763_);
lean_dec(v_d_1761_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1773_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1768_ = lean_box(0);
v___x_1769_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_erased_1764_, v_thmId_1762_, v___x_1768_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v___x_1769_);
v___x_1771_ = v___x_1766_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_specs_1763_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0(lean_object* v_00_u03b2_1774_, lean_object* v_x_1775_, lean_object* v_x_1776_, lean_object* v_x_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_x_1775_, v_x_1776_, v_x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(lean_object* v_00_u03b2_1779_, lean_object* v_x_1780_, size_t v_x_1781_, size_t v_x_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_1780_, v_x_1781_, v_x_1782_, v_x_1783_, v_x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
size_t v_x_618__boxed_1792_; size_t v_x_619__boxed_1793_; lean_object* v_res_1794_; 
v_x_618__boxed_1792_ = lean_unbox_usize(v_x_1788_);
lean_dec(v_x_1788_);
v_x_619__boxed_1793_ = lean_unbox_usize(v_x_1789_);
lean_dec(v_x_1789_);
v_res_1794_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(v_00_u03b2_1786_, v_x_1787_, v_x_618__boxed_1792_, v_x_619__boxed_1793_, v_x_1790_, v_x_1791_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1795_, lean_object* v_n_1796_, lean_object* v_k_1797_, lean_object* v_v_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v_n_1796_, v_k_1797_, v_v_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1800_, size_t v_depth_1801_, lean_object* v_keys_1802_, lean_object* v_vals_1803_, lean_object* v_heq_1804_, lean_object* v_i_1805_, lean_object* v_entries_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_1801_, v_keys_1802_, v_vals_1803_, v_i_1805_, v_entries_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1808_, lean_object* v_depth_1809_, lean_object* v_keys_1810_, lean_object* v_vals_1811_, lean_object* v_heq_1812_, lean_object* v_i_1813_, lean_object* v_entries_1814_){
_start:
{
size_t v_depth_boxed_1815_; lean_object* v_res_1816_; 
v_depth_boxed_1815_ = lean_unbox_usize(v_depth_1809_);
lean_dec(v_depth_1809_);
v_res_1816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(v_00_u03b2_1808_, v_depth_boxed_1815_, v_keys_1810_, v_vals_1811_, v_heq_1812_, v_i_1813_, v_entries_1814_);
lean_dec_ref(v_vals_1811_);
lean_dec_ref(v_keys_1810_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1818_, v_x_1819_, v_x_1820_, v_x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(lean_object* v_a_1823_, lean_object* v_as_1824_, size_t v_i_1825_, size_t v_stop_1826_){
_start:
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_usize_dec_eq(v_i_1825_, v_stop_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = lean_array_uget_borrowed(v_as_1824_, v_i_1825_);
v___x_1829_ = lean_expr_eqv(v_a_1823_, v___x_1828_);
if (v___x_1829_ == 0)
{
size_t v___x_1830_; size_t v___x_1831_; 
v___x_1830_ = ((size_t)1ULL);
v___x_1831_ = lean_usize_add(v_i_1825_, v___x_1830_);
v_i_1825_ = v___x_1831_;
goto _start;
}
else
{
return v___x_1829_;
}
}
else
{
uint8_t v___x_1833_; 
v___x_1833_ = 0;
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0___boxed(lean_object* v_a_1834_, lean_object* v_as_1835_, lean_object* v_i_1836_, lean_object* v_stop_1837_){
_start:
{
size_t v_i_boxed_1838_; size_t v_stop_boxed_1839_; uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_i_boxed_1838_ = lean_unbox_usize(v_i_1836_);
lean_dec(v_i_1836_);
v_stop_boxed_1839_ = lean_unbox_usize(v_stop_1837_);
lean_dec(v_stop_1837_);
v_res_1840_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(v_a_1834_, v_as_1835_, v_i_boxed_1838_, v_stop_boxed_1839_);
lean_dec_ref(v_as_1835_);
lean_dec_ref(v_a_1834_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(lean_object* v_as_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_array_get_size(v_as_1842_);
v___x_1846_ = lean_nat_dec_lt(v___x_1844_, v___x_1845_);
if (v___x_1846_ == 0)
{
return v___x_1846_;
}
else
{
if (v___x_1846_ == 0)
{
return v___x_1846_;
}
else
{
size_t v___x_1847_; size_t v___x_1848_; uint8_t v___x_1849_; 
v___x_1847_ = ((size_t)0ULL);
v___x_1848_ = lean_usize_of_nat(v___x_1845_);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(v_a_1843_, v_as_1842_, v___x_1847_, v___x_1848_);
return v___x_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0___boxed(lean_object* v_as_1850_, lean_object* v_a_1851_){
_start:
{
uint8_t v_res_1852_; lean_object* v_r_1853_; 
v_res_1852_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_as_1850_, v_a_1851_);
lean_dec_ref(v_a_1851_);
lean_dec_ref(v_as_1850_);
v_r_1853_ = lean_box(v_res_1852_);
return v_r_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(lean_object* v_xs_1857_, lean_object* v_e_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_ty_1865_; lean_object* v_b_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; uint8_t v___x_1883_; 
v___x_1883_ = l_Lean_Expr_hasExprMVar(v_e_1858_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_unsigned_to_nat(0u);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
else
{
switch(lean_obj_tag(v_e_1858_))
{
case 5:
{
lean_object* v_fn_1886_; lean_object* v_arg_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v_fn_1886_ = lean_ctor_get(v_e_1858_, 0);
v_arg_1887_ = lean_ctor_get(v_e_1858_, 1);
v___x_1888_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1));
v___x_1889_ = lean_unsigned_to_nat(3u);
v___x_1890_ = l_Lean_Expr_isAppOfArity(v_e_1858_, v___x_1888_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
v___x_1891_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1857_, v_fn_1886_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v___x_1891_);
v___x_1893_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1857_, v_arg_1887_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1902_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = lean_nat_add(v_a_1892_, v_a_1894_);
lean_dec(v_a_1894_);
lean_dec(v_a_1892_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_dec(v_a_1892_);
return v___x_1893_;
}
}
else
{
return v___x_1891_;
}
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v_l_1919_; lean_object* v_r_1920_; uint8_t v___y_1922_; uint8_t v___y_1930_; uint8_t v___x_1934_; 
v___x_1903_ = l_Lean_Expr_appFn_x21(v_e_1858_);
v___x_1904_ = l_Lean_Expr_appArg_x21(v___x_1903_);
lean_dec_ref(v___x_1903_);
v___x_1905_ = l_Lean_Expr_appArg_x21(v_e_1858_);
v_l_1919_ = l_Lean_Expr_getAppFn_x27(v___x_1904_);
v_r_1920_ = l_Lean_Expr_getAppFn_x27(v___x_1905_);
v___x_1934_ = l_Lean_Expr_isMVar(v_l_1919_);
if (v___x_1934_ == 0)
{
v___y_1930_ = v___x_1934_;
goto v___jp_1929_;
}
else
{
uint8_t v___x_1935_; 
v___x_1935_ = l_Lean_Expr_hasLooseBVars(v___x_1905_);
v___y_1930_ = v___x_1935_;
goto v___jp_1929_;
}
v___jp_1906_:
{
lean_object* v___x_1907_; 
v___x_1907_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1857_, v___x_1904_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
lean_dec_ref(v___x_1904_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1909_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref(v___x_1907_);
v___x_1909_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1857_, v___x_1905_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
lean_dec_ref(v___x_1905_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1918_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_nat_add(v_a_1908_, v_a_1910_);
lean_dec(v_a_1910_);
lean_dec(v_a_1908_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1914_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_dec(v_a_1908_);
return v___x_1909_;
}
}
else
{
lean_dec_ref(v___x_1905_);
return v___x_1907_;
}
}
v___jp_1921_:
{
if (v___y_1922_ == 0)
{
lean_dec_ref(v_r_1920_);
goto v___jp_1906_;
}
else
{
uint8_t v___x_1923_; 
v___x_1923_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_xs_1857_, v_r_1920_);
lean_dec_ref(v_r_1920_);
if (v___x_1923_ == 0)
{
goto v___jp_1906_;
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_dec_ref(v___x_1905_);
lean_dec_ref(v___x_1904_);
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
return v___x_1925_;
}
}
}
v___jp_1926_:
{
uint8_t v___x_1927_; 
v___x_1927_ = l_Lean_Expr_isMVar(v_r_1920_);
if (v___x_1927_ == 0)
{
v___y_1922_ = v___x_1927_;
goto v___jp_1921_;
}
else
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Expr_hasLooseBVars(v___x_1904_);
v___y_1922_ = v___x_1928_;
goto v___jp_1921_;
}
}
v___jp_1929_:
{
if (v___y_1930_ == 0)
{
lean_dec_ref(v_l_1919_);
goto v___jp_1926_;
}
else
{
uint8_t v___x_1931_; 
v___x_1931_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_xs_1857_, v_l_1919_);
lean_dec_ref(v_l_1919_);
if (v___x_1931_ == 0)
{
goto v___jp_1926_;
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_dec_ref(v_r_1920_);
lean_dec_ref(v___x_1905_);
lean_dec_ref(v___x_1904_);
v___x_1932_ = lean_unsigned_to_nat(1u);
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
return v___x_1933_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_1936_; lean_object* v_body_1937_; 
v_binderType_1936_ = lean_ctor_get(v_e_1858_, 1);
v_body_1937_ = lean_ctor_get(v_e_1858_, 2);
v_ty_1865_ = v_binderType_1936_;
v_b_1866_ = v_body_1937_;
v___y_1867_ = v_a_1859_;
v___y_1868_ = v_a_1860_;
v___y_1869_ = v_a_1861_;
v___y_1870_ = v_a_1862_;
goto v___jp_1864_;
}
case 7:
{
lean_object* v_binderType_1938_; lean_object* v_body_1939_; 
v_binderType_1938_ = lean_ctor_get(v_e_1858_, 1);
v_body_1939_ = lean_ctor_get(v_e_1858_, 2);
v_ty_1865_ = v_binderType_1938_;
v_b_1866_ = v_body_1939_;
v___y_1867_ = v_a_1859_;
v___y_1868_ = v_a_1860_;
v___y_1869_ = v_a_1861_;
v___y_1870_ = v_a_1862_;
goto v___jp_1864_;
}
case 8:
{
lean_object* v_type_1940_; lean_object* v_value_1941_; lean_object* v_body_1942_; lean_object* v___x_1943_; 
v_type_1940_ = lean_ctor_get(v_e_1858_, 1);
v_value_1941_ = lean_ctor_get(v_e_1858_, 2);
v_body_1942_ = lean_ctor_get(v_e_1858_, 3);
v___x_1943_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1857_, v_type_1940_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1857_, v_value_1941_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1947_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
v___x_1947_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1857_, v_body_1942_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1957_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1957_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1957_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1952_ = lean_nat_add(v_a_1944_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec(v_a_1944_);
v___x_1953_ = lean_nat_add(v___x_1952_, v_a_1948_);
lean_dec(v_a_1948_);
lean_dec(v___x_1952_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1953_);
v___x_1955_ = v___x_1950_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
else
{
lean_dec(v_a_1946_);
lean_dec(v_a_1944_);
return v___x_1947_;
}
}
else
{
lean_dec(v_a_1944_);
return v___x_1945_;
}
}
else
{
return v___x_1943_;
}
}
case 10:
{
lean_object* v_expr_1958_; 
v_expr_1958_ = lean_ctor_get(v_e_1858_, 1);
v_e_1858_ = v_expr_1958_;
goto _start;
}
case 11:
{
lean_object* v_struct_1960_; 
v_struct_1960_ = lean_ctor_get(v_e_1858_, 2);
v_e_1858_ = v_struct_1960_;
goto _start;
}
default: 
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
}
}
v___jp_1864_:
{
lean_object* v___x_1871_; 
v___x_1871_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1857_, v_ty_1865_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1873_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref(v___x_1871_);
v___x_1873_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1857_, v_b_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_nat_add(v_a_1872_, v_a_1874_);
lean_dec(v_a_1874_);
lean_dec(v_a_1872_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_dec(v_a_1872_);
return v___x_1873_;
}
}
else
{
return v___x_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___boxed(lean_object* v_xs_1964_, lean_object* v_e_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1964_, v_e_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec_ref(v_e_1965_);
lean_dec_ref(v_xs_1964_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(lean_object* v_xs_1972_, lean_object* v_e_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1972_, v_e_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars___boxed(lean_object* v_xs_1980_, lean_object* v_e_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(v_xs_1980_, v_e_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec_ref(v_e_1981_);
lean_dec_ref(v_xs_1980_);
return v_res_1987_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig(void){
_start:
{
lean_object* v___x_1988_; lean_object* v_config_1989_; uint8_t v_foApprox_1990_; uint8_t v_ctxApprox_1991_; uint8_t v_quasiPatternApprox_1992_; uint8_t v_constApprox_1993_; uint8_t v_isDefEqStuckEx_1994_; uint8_t v_unificationHints_1995_; uint8_t v_proofIrrelevance_1996_; uint8_t v_assignSyntheticOpaque_1997_; uint8_t v_offsetCnstrs_1998_; uint8_t v_transparency_1999_; uint8_t v_etaStruct_2000_; uint8_t v_univApprox_2001_; uint8_t v_zetaUnused_2002_; uint8_t v_zetaHave_2003_; uint8_t v___x_2004_; uint8_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_1988_ = l_Lean_Meta_simpGlobalConfig;
v_config_1989_ = lean_ctor_get(v___x_1988_, 0);
v_foApprox_1990_ = lean_ctor_get_uint8(v_config_1989_, 0);
v_ctxApprox_1991_ = lean_ctor_get_uint8(v_config_1989_, 1);
v_quasiPatternApprox_1992_ = lean_ctor_get_uint8(v_config_1989_, 2);
v_constApprox_1993_ = lean_ctor_get_uint8(v_config_1989_, 3);
v_isDefEqStuckEx_1994_ = lean_ctor_get_uint8(v_config_1989_, 4);
v_unificationHints_1995_ = lean_ctor_get_uint8(v_config_1989_, 5);
v_proofIrrelevance_1996_ = lean_ctor_get_uint8(v_config_1989_, 6);
v_assignSyntheticOpaque_1997_ = lean_ctor_get_uint8(v_config_1989_, 7);
v_offsetCnstrs_1998_ = lean_ctor_get_uint8(v_config_1989_, 8);
v_transparency_1999_ = lean_ctor_get_uint8(v_config_1989_, 9);
v_etaStruct_2000_ = lean_ctor_get_uint8(v_config_1989_, 10);
v_univApprox_2001_ = lean_ctor_get_uint8(v_config_1989_, 11);
v_zetaUnused_2002_ = lean_ctor_get_uint8(v_config_1989_, 17);
v_zetaHave_2003_ = lean_ctor_get_uint8(v_config_1989_, 18);
v___x_2004_ = 1;
v___x_2005_ = 2;
v___x_2006_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2006_, 0, v_foApprox_1990_);
lean_ctor_set_uint8(v___x_2006_, 1, v_ctxApprox_1991_);
lean_ctor_set_uint8(v___x_2006_, 2, v_quasiPatternApprox_1992_);
lean_ctor_set_uint8(v___x_2006_, 3, v_constApprox_1993_);
lean_ctor_set_uint8(v___x_2006_, 4, v_isDefEqStuckEx_1994_);
lean_ctor_set_uint8(v___x_2006_, 5, v_unificationHints_1995_);
lean_ctor_set_uint8(v___x_2006_, 6, v_proofIrrelevance_1996_);
lean_ctor_set_uint8(v___x_2006_, 7, v_assignSyntheticOpaque_1997_);
lean_ctor_set_uint8(v___x_2006_, 8, v_offsetCnstrs_1998_);
lean_ctor_set_uint8(v___x_2006_, 9, v_transparency_1999_);
lean_ctor_set_uint8(v___x_2006_, 10, v_etaStruct_2000_);
lean_ctor_set_uint8(v___x_2006_, 11, v_univApprox_2001_);
lean_ctor_set_uint8(v___x_2006_, 12, v___x_2004_);
lean_ctor_set_uint8(v___x_2006_, 13, v___x_2004_);
lean_ctor_set_uint8(v___x_2006_, 14, v___x_2005_);
lean_ctor_set_uint8(v___x_2006_, 15, v___x_2004_);
lean_ctor_set_uint8(v___x_2006_, 16, v___x_2004_);
lean_ctor_set_uint8(v___x_2006_, 17, v_zetaUnused_2002_);
lean_ctor_set_uint8(v___x_2006_, 18, v_zetaHave_2003_);
v___x_2007_ = l_Lean_Meta_Config_toConfigWithKey(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(lean_object* v_k_2008_, uint8_t v_allowLevelAssignments_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2009_, v_k_2008_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v_a_2024_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2015_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2015_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg___boxed(lean_object* v_k_2032_, lean_object* v_allowLevelAssignments_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2039_; lean_object* v_res_2040_; 
v_allowLevelAssignments_boxed_2039_ = lean_unbox(v_allowLevelAssignments_2033_);
v_res_2040_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_2032_, v_allowLevelAssignments_boxed_2039_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(lean_object* v_00_u03b1_2041_, lean_object* v_k_2042_, uint8_t v_allowLevelAssignments_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_2042_, v_allowLevelAssignments_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___boxed(lean_object* v_00_u03b1_2050_, lean_object* v_k_2051_, lean_object* v_allowLevelAssignments_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2058_; lean_object* v_res_2059_; 
v_allowLevelAssignments_boxed_2058_ = lean_unbox(v_allowLevelAssignments_2052_);
v_res_2059_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(v_00_u03b1_2050_, v_k_2051_, v_allowLevelAssignments_boxed_2058_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2059_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2067_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5);
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v___x_2070_);
return v___x_2072_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_unsigned_to_nat(32u);
v___x_2074_ = lean_mk_empty_array_with_capacity(v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8(void){
_start:
{
size_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2076_ = ((size_t)5ULL);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = lean_unsigned_to_nat(32u);
v___x_2079_ = lean_mk_empty_array_with_capacity(v___x_2078_);
v___x_2080_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7);
v___x_2081_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v___x_2079_);
lean_ctor_set(v___x_2081_, 2, v___x_2077_);
lean_ctor_set(v___x_2081_, 3, v___x_2077_);
lean_ctor_set_usize(v___x_2081_, 4, v___x_2076_);
return v___x_2081_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8);
v___x_2083_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5);
v___x_2084_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
lean_ctor_set(v___x_2084_, 2, v___x_2083_);
lean_ctor_set(v___x_2084_, 3, v___x_2082_);
return v___x_2084_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9);
v___x_2086_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___x_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(lean_object* v_a_2088_, lean_object* v_xs_2089_, lean_object* v_b_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_snd_2096_; lean_object* v_snd_2097_; lean_object* v_snd_2098_; lean_object* v_fst_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2226_; 
v_snd_2096_ = lean_ctor_get(v_b_2090_, 1);
lean_inc(v_snd_2096_);
v_snd_2097_ = lean_ctor_get(v_snd_2096_, 1);
lean_inc(v_snd_2097_);
v_snd_2098_ = lean_ctor_get(v_snd_2097_, 1);
lean_inc(v_snd_2098_);
v_fst_2099_ = lean_ctor_get(v_b_2090_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_b_2090_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; 
v_unused_2227_ = lean_ctor_get(v_b_2090_, 1);
lean_dec(v_unused_2227_);
v___x_2101_ = v_b_2090_;
v_isShared_2102_ = v_isSharedCheck_2226_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_fst_2099_);
lean_dec(v_b_2090_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2226_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_fst_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2224_; 
v_fst_2103_ = lean_ctor_get(v_snd_2096_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_snd_2096_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; 
v_unused_2225_ = lean_ctor_get(v_snd_2096_, 1);
lean_dec(v_unused_2225_);
v___x_2105_ = v_snd_2096_;
v_isShared_2106_ = v_isSharedCheck_2224_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_fst_2103_);
lean_dec(v_snd_2096_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2224_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_fst_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2222_; 
v_fst_2107_ = lean_ctor_get(v_snd_2097_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_snd_2097_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v_snd_2097_, 1);
lean_dec(v_unused_2223_);
v___x_2109_ = v_snd_2097_;
v_isShared_2110_ = v_isSharedCheck_2222_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_fst_2107_);
lean_dec(v_snd_2097_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2222_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_fst_2111_; lean_object* v_snd_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2221_; 
v_fst_2111_ = lean_ctor_get(v_snd_2098_, 0);
v_snd_2112_ = lean_ctor_get(v_snd_2098_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_snd_2098_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2114_ = v_snd_2098_;
v_isShared_2115_ = v_isSharedCheck_2221_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_snd_2112_);
lean_inc(v_fst_2111_);
lean_dec(v_snd_2098_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2221_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2116_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__2));
v___x_2117_ = lean_unsigned_to_nat(3u);
v___x_2118_ = l_Lean_Expr_isAppOfArity(v_fst_2099_, v___x_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2120_; 
lean_dec_ref(v_a_2088_);
if (v_isShared_2115_ == 0)
{
v___x_2120_ = v___x_2114_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_fst_2111_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_snd_2112_);
v___x_2120_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2122_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v___x_2120_);
v___x_2122_ = v___x_2109_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_fst_2107_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2124_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v___x_2122_);
v___x_2124_ = v___x_2105_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_fst_2103_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2126_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 1, v___x_2124_);
v___x_2126_ = v___x_2101_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_fst_2099_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
}
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_del_object(v___x_2101_);
v___x_2132_ = lean_unsigned_to_nat(1u);
v___x_2133_ = l_Lean_Expr_getAppNumArgs(v_fst_2099_);
v___x_2134_ = lean_nat_sub(v___x_2133_, v___x_2132_);
v___x_2135_ = lean_nat_sub(v___x_2134_, v___x_2132_);
lean_dec(v___x_2134_);
v___x_2136_ = l_Lean_Expr_getRevArg_x21(v_fst_2099_, v___x_2135_);
v___x_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
v___x_2138_ = 0;
v___x_2139_ = lean_box(0);
v___x_2140_ = l_Lean_Meta_mkFreshExprMVar(v___x_2137_, v___x_2138_, v___x_2139_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref(v___x_2140_);
v___x_2142_ = lean_mk_empty_array_with_capacity(v___x_2132_);
v___x_2143_ = lean_array_push(v___x_2142_, v_a_2141_);
v___x_2144_ = l_Lean_Expr_beta(v_fst_2103_, v___x_2143_);
v___x_2145_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__3));
v___x_2146_ = lean_box(0);
v___x_2147_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10);
lean_inc_ref(v_a_2088_);
v___x_2148_ = l_Lean_Meta_simp(v___x_2144_, v_a_2088_, v___x_2145_, v___x_2146_, v___x_2147_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v_fst_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2203_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
v_fst_2150_ = lean_ctor_get(v_a_2149_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_a_2149_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; 
v_unused_2204_ = lean_ctor_get(v_a_2149_, 1);
lean_dec(v_unused_2204_);
v___x_2152_ = v_a_2149_;
v_isShared_2153_ = v_isSharedCheck_2203_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_fst_2150_);
lean_dec(v_a_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2203_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_expr_2154_; lean_object* v___x_2155_; 
v_expr_2154_ = lean_ctor_get(v_fst_2150_, 0);
lean_inc_ref(v_expr_2154_);
lean_dec(v_fst_2150_);
v___x_2155_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2089_, v_expr_2154_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; lean_object* v_lastSuccess_2159_; lean_object* v_boundAssignments_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; uint8_t v___x_2192_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = lean_nat_add(v_fst_2107_, v___x_2132_);
lean_dec(v_fst_2107_);
v___x_2192_ = lean_nat_dec_lt(v_a_2156_, v_snd_2112_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = l_Lean_Expr_getAppFn_x27(v_expr_2154_);
v___x_2194_ = l_Lean_Expr_isMVar(v___x_2193_);
lean_dec_ref(v___x_2193_);
if (v___x_2194_ == 0)
{
lean_dec(v_a_2156_);
v_lastSuccess_2159_ = v_fst_2111_;
v_boundAssignments_2160_ = v_snd_2112_;
v___y_2161_ = v___y_2091_;
v___y_2162_ = v___y_2092_;
v___y_2163_ = v___y_2093_;
v___y_2164_ = v___y_2094_;
goto v___jp_2158_;
}
else
{
lean_dec(v_snd_2112_);
lean_dec(v_fst_2111_);
lean_inc(v___x_2157_);
v_lastSuccess_2159_ = v___x_2157_;
v_boundAssignments_2160_ = v_a_2156_;
v___y_2161_ = v___y_2091_;
v___y_2162_ = v___y_2092_;
v___y_2163_ = v___y_2093_;
v___y_2164_ = v___y_2094_;
goto v___jp_2158_;
}
}
else
{
lean_dec(v_snd_2112_);
lean_dec(v_fst_2111_);
lean_inc(v___x_2157_);
v_lastSuccess_2159_ = v___x_2157_;
v_boundAssignments_2160_ = v_a_2156_;
v___y_2161_ = v___y_2091_;
v___y_2162_ = v___y_2092_;
v___y_2163_ = v___y_2093_;
v___y_2164_ = v___y_2094_;
goto v___jp_2158_;
}
v___jp_2158_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2165_ = lean_unsigned_to_nat(2u);
v___x_2166_ = lean_nat_sub(v___x_2133_, v___x_2165_);
lean_dec(v___x_2133_);
v___x_2167_ = lean_nat_sub(v___x_2166_, v___x_2132_);
lean_dec(v___x_2166_);
v___x_2168_ = l_Lean_Expr_getRevArg_x21(v_fst_2099_, v___x_2167_);
lean_dec(v_fst_2099_);
v___x_2169_ = l_Lean_Meta_whnfR(v___x_2168_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref(v___x_2169_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v_boundAssignments_2160_);
lean_ctor_set(v___x_2152_, 0, v_lastSuccess_2159_);
v___x_2172_ = v___x_2152_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_lastSuccess_2159_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_boundAssignments_2160_);
v___x_2172_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2174_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v___x_2172_);
lean_ctor_set(v___x_2114_, 0, v___x_2157_);
v___x_2174_ = v___x_2114_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2176_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v___x_2174_);
lean_ctor_set(v___x_2109_, 0, v_expr_2154_);
v___x_2176_ = v___x_2109_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_expr_2154_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2178_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v___x_2176_);
lean_ctor_set(v___x_2105_, 0, v_a_2170_);
v___x_2178_ = v___x_2105_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2170_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
v_b_2090_ = v___x_2178_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_boundAssignments_2160_);
lean_dec(v_lastSuccess_2159_);
lean_dec(v___x_2157_);
lean_dec_ref(v_expr_2154_);
lean_del_object(v___x_2152_);
lean_del_object(v___x_2114_);
lean_del_object(v___x_2109_);
lean_del_object(v___x_2105_);
lean_dec_ref(v_a_2088_);
v_a_2184_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2169_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2169_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec_ref(v_expr_2154_);
lean_del_object(v___x_2152_);
lean_dec(v___x_2133_);
lean_del_object(v___x_2114_);
lean_dec(v_snd_2112_);
lean_dec(v_fst_2111_);
lean_del_object(v___x_2109_);
lean_dec(v_fst_2107_);
lean_del_object(v___x_2105_);
lean_dec(v_fst_2099_);
lean_dec_ref(v_a_2088_);
v_a_2195_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2155_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2155_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v___x_2133_);
lean_del_object(v___x_2114_);
lean_dec(v_snd_2112_);
lean_dec(v_fst_2111_);
lean_del_object(v___x_2109_);
lean_dec(v_fst_2107_);
lean_del_object(v___x_2105_);
lean_dec(v_fst_2099_);
lean_dec_ref(v_a_2088_);
v_a_2205_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2148_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2148_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v___x_2133_);
lean_del_object(v___x_2114_);
lean_dec(v_snd_2112_);
lean_dec(v_fst_2111_);
lean_del_object(v___x_2109_);
lean_dec(v_fst_2107_);
lean_del_object(v___x_2105_);
lean_dec(v_fst_2103_);
lean_dec(v_fst_2099_);
lean_dec_ref(v_a_2088_);
v_a_2213_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2140_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2140_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___boxed(lean_object* v_a_2228_, lean_object* v_xs_2229_, lean_object* v_b_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(v_a_2228_, v_xs_2229_, v_b_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec_ref(v_xs_2229_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(lean_object* v___x_2237_, uint8_t v___x_2238_, lean_object* v_00_u03c3s_2239_, lean_object* v_xs_2240_, lean_object* v_e_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
if (v___x_2238_ == 0)
{
lean_object* v_config_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2321_; 
v_config_2247_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2249_ = v___x_2237_;
v_isShared_2250_ = v_isSharedCheck_2321_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_config_2247_);
lean_dec(v___x_2237_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2321_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
uint8_t v_trackZetaDelta_2251_; lean_object* v_zetaDeltaSet_2252_; lean_object* v_lctx_2253_; lean_object* v_localInstances_2254_; lean_object* v_defEqCtx_x3f_2255_; lean_object* v_synthPendingDepth_2256_; lean_object* v_canUnfold_x3f_2257_; uint8_t v_univApprox_2258_; uint8_t v_inTypeClassResolution_2259_; uint8_t v_cacheInferType_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2319_; 
v_trackZetaDelta_2251_ = lean_ctor_get_uint8(v___y_2242_, sizeof(void*)*7);
v_zetaDeltaSet_2252_ = lean_ctor_get(v___y_2242_, 1);
v_lctx_2253_ = lean_ctor_get(v___y_2242_, 2);
v_localInstances_2254_ = lean_ctor_get(v___y_2242_, 3);
v_defEqCtx_x3f_2255_ = lean_ctor_get(v___y_2242_, 4);
v_synthPendingDepth_2256_ = lean_ctor_get(v___y_2242_, 5);
v_canUnfold_x3f_2257_ = lean_ctor_get(v___y_2242_, 6);
v_univApprox_2258_ = lean_ctor_get_uint8(v___y_2242_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2259_ = lean_ctor_get_uint8(v___y_2242_, sizeof(void*)*7 + 2);
v_cacheInferType_2260_ = lean_ctor_get_uint8(v___y_2242_, sizeof(void*)*7 + 3);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___y_2242_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v___y_2242_, 0);
lean_dec(v_unused_2320_);
v___x_2262_ = v___y_2242_;
v_isShared_2263_ = v_isSharedCheck_2319_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_canUnfold_x3f_2257_);
lean_inc(v_synthPendingDepth_2256_);
lean_inc(v_defEqCtx_x3f_2255_);
lean_inc(v_localInstances_2254_);
lean_inc(v_lctx_2253_);
lean_inc(v_zetaDeltaSet_2252_);
lean_dec(v___y_2242_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2319_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
uint64_t v___x_2264_; lean_object* v___x_2266_; 
v___x_2264_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2247_);
if (v_isShared_2250_ == 0)
{
v___x_2266_ = v___x_2249_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_config_2247_);
v___x_2266_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2268_; 
lean_ctor_set_uint64(v___x_2266_, sizeof(void*)*1, v___x_2264_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2266_);
v___x_2268_ = v___x_2262_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_zetaDeltaSet_2252_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v_lctx_2253_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v_localInstances_2254_);
lean_ctor_set(v_reuseFailAlloc_2317_, 4, v_defEqCtx_x3f_2255_);
lean_ctor_set(v_reuseFailAlloc_2317_, 5, v_synthPendingDepth_2256_);
lean_ctor_set(v_reuseFailAlloc_2317_, 6, v_canUnfold_x3f_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2317_, sizeof(void*)*7, v_trackZetaDelta_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2317_, sizeof(void*)*7 + 1, v_univApprox_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2317_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2317_, sizeof(void*)*7 + 3, v_cacheInferType_2260_);
v___x_2268_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v___x_2268_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v___x_2269_);
v___x_2271_ = l_Lean_Meta_whnfR(v_00_u03c3s_2239_, v___x_2268_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref(v___x_2271_);
v___x_2273_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2240_, v_e_2241_, v___x_2268_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref(v___x_2273_);
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
lean_ctor_set(v___x_2276_, 1, v_a_2274_);
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v_e_2241_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2279_, 0, v_a_2272_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(v_a_2270_, v_xs_2240_, v___x_2279_, v___x_2268_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec_ref(v___x_2268_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2292_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2292_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2292_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v_snd_2285_; lean_object* v_snd_2286_; lean_object* v_snd_2287_; lean_object* v_fst_2288_; lean_object* v___x_2290_; 
v_snd_2285_ = lean_ctor_get(v_a_2281_, 1);
lean_inc(v_snd_2285_);
lean_dec(v_a_2281_);
v_snd_2286_ = lean_ctor_get(v_snd_2285_, 1);
lean_inc(v_snd_2286_);
lean_dec(v_snd_2285_);
v_snd_2287_ = lean_ctor_get(v_snd_2286_, 1);
lean_inc(v_snd_2287_);
lean_dec(v_snd_2286_);
v_fst_2288_ = lean_ctor_get(v_snd_2287_, 0);
lean_inc(v_fst_2288_);
lean_dec(v_snd_2287_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v_fst_2288_);
v___x_2290_ = v___x_2283_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_fst_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
v_a_2293_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2280_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2280_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_dec(v_a_2272_);
lean_dec(v_a_2270_);
lean_dec_ref(v___x_2268_);
lean_dec_ref(v_e_2241_);
return v___x_2273_;
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec(v_a_2270_);
lean_dec_ref(v___x_2268_);
lean_dec_ref(v_e_2241_);
v_a_2301_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2271_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2271_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v___x_2268_);
lean_dec_ref(v_e_2241_);
lean_dec_ref(v_00_u03c3s_2239_);
v_a_2309_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2269_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2269_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
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
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_e_2241_);
lean_dec_ref(v_00_u03c3s_2239_);
lean_dec_ref(v___x_2237_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed(lean_object* v___x_2324_, lean_object* v___x_2325_, lean_object* v_00_u03c3s_2326_, lean_object* v_xs_2327_, lean_object* v_e_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
uint8_t v___x_4177__boxed_2334_; lean_object* v_res_2335_; 
v___x_4177__boxed_2334_ = lean_unbox(v___x_2325_);
v_res_2335_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(v___x_2324_, v___x_4177__boxed_2334_, v_00_u03c3s_2326_, v_xs_2327_, v_e_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v_xs_2327_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(lean_object* v_xs_2336_, lean_object* v_00_u03c3s_2337_, lean_object* v_e_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___f_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; 
v___x_2344_ = l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig;
v___x_2345_ = lean_array_get_size(v_xs_2336_);
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_nat_dec_eq(v___x_2345_, v___x_2346_);
v___x_2348_ = lean_box(v___x_2347_);
v___f_2349_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2349_, 0, v___x_2344_);
lean_closure_set(v___f_2349_, 1, v___x_2348_);
lean_closure_set(v___f_2349_, 2, v_00_u03c3s_2337_);
lean_closure_set(v___f_2349_, 3, v_xs_2336_);
lean_closure_set(v___f_2349_, 4, v_e_2338_);
v___x_2350_ = 0;
v___x_2351_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_2349_, v___x_2350_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___boxed(lean_object* v_xs_2352_, lean_object* v_00_u03c3s_2353_, lean_object* v_e_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_xs_2352_, v_00_u03c3s_2353_, v_e_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
return v_res_2360_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0));
v___x_2363_ = l_Lean_stringToMessageData(v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(lean_object* v_a_2377_, lean_object* v___x_2378_, uint8_t v___x_2379_, lean_object* v___x_2380_, lean_object* v_proof_2381_, lean_object* v_prio_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; lean_object* v_config_2389_; uint8_t v_trackZetaDelta_2390_; lean_object* v_zetaDeltaSet_2391_; lean_object* v_lctx_2392_; lean_object* v_localInstances_2393_; lean_object* v_defEqCtx_x3f_2394_; lean_object* v_synthPendingDepth_2395_; lean_object* v_canUnfold_x3f_2396_; uint8_t v_univApprox_2397_; uint8_t v_inTypeClassResolution_2398_; uint8_t v_cacheInferType_2399_; uint64_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2388_ = l_Lean_Meta_simpGlobalConfig;
v_config_2389_ = lean_ctor_get(v___x_2388_, 0);
v_trackZetaDelta_2390_ = lean_ctor_get_uint8(v___y_2383_, sizeof(void*)*7);
v_zetaDeltaSet_2391_ = lean_ctor_get(v___y_2383_, 1);
v_lctx_2392_ = lean_ctor_get(v___y_2383_, 2);
v_localInstances_2393_ = lean_ctor_get(v___y_2383_, 3);
v_defEqCtx_x3f_2394_ = lean_ctor_get(v___y_2383_, 4);
v_synthPendingDepth_2395_ = lean_ctor_get(v___y_2383_, 5);
v_canUnfold_x3f_2396_ = lean_ctor_get(v___y_2383_, 6);
v_univApprox_2397_ = lean_ctor_get_uint8(v___y_2383_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2398_ = lean_ctor_get_uint8(v___y_2383_, sizeof(void*)*7 + 2);
v_cacheInferType_2399_ = lean_ctor_get_uint8(v___y_2383_, sizeof(void*)*7 + 3);
v___x_2400_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2389_);
lean_inc_ref(v_config_2389_);
v___x_2401_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2401_, 0, v_config_2389_);
lean_ctor_set_uint64(v___x_2401_, sizeof(void*)*1, v___x_2400_);
lean_inc(v_canUnfold_x3f_2396_);
lean_inc(v_synthPendingDepth_2395_);
lean_inc(v_defEqCtx_x3f_2394_);
lean_inc_ref(v_localInstances_2393_);
lean_inc_ref(v_lctx_2392_);
lean_inc(v_zetaDeltaSet_2391_);
v___x_2402_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v_zetaDeltaSet_2391_);
lean_ctor_set(v___x_2402_, 2, v_lctx_2392_);
lean_ctor_set(v___x_2402_, 3, v_localInstances_2393_);
lean_ctor_set(v___x_2402_, 4, v_defEqCtx_x3f_2394_);
lean_ctor_set(v___x_2402_, 5, v_synthPendingDepth_2395_);
lean_ctor_set(v___x_2402_, 6, v_canUnfold_x3f_2396_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*7, v_trackZetaDelta_2390_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*7 + 1, v_univApprox_2397_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2398_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*7 + 3, v_cacheInferType_2399_);
v___x_2403_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2377_, v___x_2378_, v___x_2379_, v___x_2402_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec_ref(v___x_2402_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v_snd_2405_; lean_object* v_fst_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2507_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref(v___x_2403_);
v_snd_2405_ = lean_ctor_get(v_a_2404_, 1);
v_fst_2406_ = lean_ctor_get(v_a_2404_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_a_2404_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2408_ = v_a_2404_;
v_isShared_2409_ = v_isSharedCheck_2507_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_snd_2405_);
lean_inc(v_fst_2406_);
lean_dec(v_a_2404_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2507_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v_snd_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2505_; 
v_snd_2410_ = lean_ctor_get(v_snd_2405_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_snd_2405_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v_snd_2405_, 0);
lean_dec(v_unused_2506_);
v___x_2412_ = v_snd_2405_;
v_isShared_2413_ = v_isSharedCheck_2505_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_snd_2410_);
lean_dec(v_snd_2405_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2505_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_Meta_whnfR(v_snd_2410_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_n(v_a_2415_, 2);
lean_dec_ref(v___x_2414_);
v___x_2427_ = l_Lean_Expr_cleanupAnnotations(v_a_2415_);
v___x_2428_ = l_Lean_Expr_isApp(v___x_2427_);
if (v___x_2428_ == 0)
{
lean_dec_ref(v___x_2427_);
lean_del_object(v___x_2408_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v___y_2417_ = v___y_2383_;
v___y_2418_ = v___y_2384_;
v___y_2419_ = v___y_2385_;
v___y_2420_ = v___y_2386_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2427_);
v___x_2430_ = l_Lean_Expr_isApp(v___x_2429_);
if (v___x_2430_ == 0)
{
lean_dec_ref(v___x_2429_);
lean_del_object(v___x_2408_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v___y_2417_ = v___y_2383_;
v___y_2418_ = v___y_2384_;
v___y_2419_ = v___y_2385_;
v___y_2420_ = v___y_2386_;
goto v___jp_2416_;
}
else
{
lean_object* v_arg_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v_arg_2431_ = lean_ctor_get(v___x_2429_, 1);
lean_inc_ref(v_arg_2431_);
v___x_2432_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2429_);
v___x_2433_ = l_Lean_Expr_isApp(v___x_2432_);
if (v___x_2433_ == 0)
{
lean_dec_ref(v___x_2432_);
lean_dec_ref(v_arg_2431_);
lean_del_object(v___x_2408_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v___y_2417_ = v___y_2383_;
v___y_2418_ = v___y_2384_;
v___y_2419_ = v___y_2385_;
v___y_2420_ = v___y_2386_;
goto v___jp_2416_;
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
lean_dec_ref(v_arg_2431_);
lean_del_object(v___x_2408_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v___y_2417_ = v___y_2383_;
v___y_2418_ = v___y_2384_;
v___y_2419_ = v___y_2385_;
v___y_2420_ = v___y_2386_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2437_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2435_);
v___x_2438_ = l_Lean_Expr_isApp(v___x_2437_);
if (v___x_2438_ == 0)
{
lean_dec_ref(v___x_2437_);
lean_dec_ref(v_arg_2434_);
lean_dec_ref(v_arg_2431_);
lean_del_object(v___x_2408_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v___y_2417_ = v___y_2383_;
v___y_2418_ = v___y_2384_;
v___y_2419_ = v___y_2385_;
v___y_2420_ = v___y_2386_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2437_);
v___x_2440_ = l_Lean_Expr_isApp(v___x_2439_);
if (v___x_2440_ == 0)
{
lean_dec_ref(v___x_2439_);
lean_dec_ref(v_arg_2434_);
lean_dec_ref(v_arg_2431_);
lean_del_object(v___x_2408_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v___y_2417_ = v___y_2383_;
v___y_2418_ = v___y_2384_;
v___y_2419_ = v___y_2385_;
v___y_2420_ = v___y_2386_;
goto v___jp_2416_;
}
else
{
lean_object* v_arg_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v_arg_2441_ = lean_ctor_get(v___x_2439_, 1);
lean_inc_ref(v_arg_2441_);
v___x_2442_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2439_);
v___x_2443_ = l_Lean_Expr_isApp(v___x_2442_);
if (v___x_2443_ == 0)
{
lean_dec_ref(v___x_2442_);
lean_dec_ref(v_arg_2441_);
lean_dec_ref(v_arg_2434_);
lean_dec_ref(v_arg_2431_);
lean_del_object(v___x_2408_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v___y_2417_ = v___y_2383_;
v___y_2418_ = v___y_2384_;
v___y_2419_ = v___y_2385_;
v___y_2420_ = v___y_2386_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2444_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2442_);
v___x_2445_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4));
v___x_2446_ = l_Lean_Expr_isConstOf(v___x_2444_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_dec_ref(v___x_2444_);
lean_dec_ref(v_arg_2441_);
lean_dec_ref(v_arg_2434_);
lean_dec_ref(v_arg_2431_);
lean_del_object(v___x_2408_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v___y_2417_ = v___y_2383_;
v___y_2418_ = v___y_2384_;
v___y_2419_ = v___y_2385_;
v___y_2420_ = v___y_2386_;
goto v___jp_2416_;
}
else
{
uint8_t v___x_2447_; lean_object* v___x_2448_; 
lean_dec(v_a_2415_);
lean_del_object(v___x_2412_);
v___x_2447_ = 0;
lean_inc_ref(v_arg_2434_);
v___x_2448_ = l_Lean_Meta_DiscrTree_mkPath(v_arg_2434_, v___x_2447_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref(v___x_2448_);
v___x_2450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7));
v___x_2451_ = l_Lean_Expr_constLevels_x21(v___x_2444_);
lean_dec_ref(v___x_2444_);
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = l_List_get_x21Internal___redArg(v___x_2380_, v___x_2451_, v___x_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
if (v_isShared_2409_ == 0)
{
lean_ctor_set_tag(v___x_2408_, 1);
lean_ctor_set(v___x_2408_, 1, v___x_2454_);
lean_ctor_set(v___x_2408_, 0, v___x_2453_);
v___x_2456_ = v___x_2408_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = l_Lean_mkConst(v___x_2450_, v___x_2456_);
v___x_2458_ = l_Lean_Expr_app___override(v___x_2457_, v_arg_2441_);
lean_inc(v_fst_2406_);
v___x_2459_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_fst_2406_, v___x_2458_, v_arg_2431_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref(v___x_2459_);
v___x_2461_ = 1;
v___x_2462_ = l_Lean_Meta_mkForallFVars(v_fst_2406_, v_arg_2434_, v___x_2447_, v___x_2446_, v___x_2446_, v___x_2461_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v_fst_2406_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2471_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2471_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2471_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2467_, 0, v_a_2449_);
lean_ctor_set(v___x_2467_, 1, v_a_2463_);
lean_ctor_set(v___x_2467_, 2, v_proof_2381_);
lean_ctor_set(v___x_2467_, 3, v_a_2460_);
lean_ctor_set(v___x_2467_, 4, v_prio_2382_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2467_);
v___x_2469_ = v___x_2465_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v_a_2460_);
lean_dec(v_a_2449_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v_a_2472_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2462_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2462_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v_a_2449_);
lean_dec_ref(v_arg_2434_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v_a_2480_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2459_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2459_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec_ref(v___x_2444_);
lean_dec_ref(v_arg_2441_);
lean_dec_ref(v_arg_2434_);
lean_dec_ref(v_arg_2431_);
lean_del_object(v___x_2408_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v_a_2489_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2448_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2448_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
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
v___jp_2416_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2421_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1);
v___x_2422_ = l_Lean_indentExpr(v_a_2415_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set_tag(v___x_2412_, 7);
lean_ctor_set(v___x_2412_, 1, v___x_2422_);
lean_ctor_set(v___x_2412_, 0, v___x_2421_);
v___x_2424_ = v___x_2412_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2424_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2425_;
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_del_object(v___x_2412_);
lean_del_object(v___x_2408_);
lean_dec(v_fst_2406_);
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v_a_2497_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2414_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2414_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_prio_2382_);
lean_dec_ref(v_proof_2381_);
v_a_2508_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2403_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2403_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed(lean_object* v_a_2516_, lean_object* v___x_2517_, lean_object* v___x_2518_, lean_object* v___x_2519_, lean_object* v_proof_2520_, lean_object* v_prio_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
uint8_t v___x_3663__boxed_2527_; lean_object* v_res_2528_; 
v___x_3663__boxed_2527_ = lean_unbox(v___x_2518_);
v_res_2528_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(v_a_2516_, v___x_2517_, v___x_3663__boxed_2527_, v___x_2519_, v_proof_2520_, v_prio_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___x_2519_);
return v_res_2528_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0));
v___x_2531_ = l_Lean_stringToMessageData(v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(lean_object* v_type_2532_, lean_object* v_proof_2533_, lean_object* v_prio_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v___x_2540_; lean_object* v_a_2541_; lean_object* v___x_2542_; 
v___x_2540_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_type_2532_, v_a_2536_);
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc_n(v_a_2541_, 2);
lean_dec_ref(v___x_2540_);
v___x_2542_ = l_Lean_Meta_isProp(v_a_2541_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2544_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; uint8_t v___x_2556_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___x_2542_);
v___x_2544_ = lean_box(0);
v___x_2556_ = lean_unbox(v_a_2543_);
lean_dec(v_a_2543_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_prio_2534_);
lean_dec_ref(v_proof_2533_);
v___x_2557_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1);
v___x_2558_ = l_Lean_indentExpr(v_a_2541_);
v___x_2559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2559_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
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
else
{
v___y_2546_ = v_a_2535_;
v___y_2547_ = v_a_2536_;
v___y_2548_ = v_a_2537_;
v___y_2549_ = v_a_2538_;
goto v___jp_2545_;
}
v___jp_2545_:
{
lean_object* v___x_2550_; uint8_t v___x_2551_; lean_object* v___x_2552_; lean_object* v___f_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; 
v___x_2550_ = lean_box(0);
v___x_2551_ = 0;
v___x_2552_ = lean_box(v___x_2551_);
v___f_2553_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2553_, 0, v_a_2541_);
lean_closure_set(v___f_2553_, 1, v___x_2550_);
lean_closure_set(v___f_2553_, 2, v___x_2552_);
lean_closure_set(v___f_2553_, 3, v___x_2544_);
lean_closure_set(v___f_2553_, 4, v_proof_2533_);
lean_closure_set(v___f_2553_, 5, v_prio_2534_);
v___x_2554_ = 0;
v___x_2555_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_2553_, v___x_2554_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
return v___x_2555_;
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v_a_2541_);
lean_dec(v_prio_2534_);
lean_dec_ref(v_proof_2533_);
v_a_2569_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2542_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2542_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___boxed(lean_object* v_type_2577_, lean_object* v_proof_2578_, lean_object* v_prio_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_type_2577_, v_proof_2578_, v_prio_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(lean_object* v_declName_2586_, lean_object* v_prio_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v___x_2593_; 
lean_inc(v_declName_2586_);
v___x_2593_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_2586_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref(v___x_2593_);
v___x_2595_ = l_Lean_ConstantInfo_levelParams(v_a_2594_);
lean_dec(v_a_2594_);
v___x_2596_ = lean_box(0);
v___x_2597_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_2595_, v___x_2596_);
lean_inc(v_declName_2586_);
v___x_2598_ = l_Lean_mkConst(v_declName_2586_, v___x_2597_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
v___x_2599_ = lean_infer_type(v___x_2598_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref(v___x_2599_);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_declName_2586_);
v___x_2602_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_2600_, v___x_2601_, v_prio_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
return v___x_2602_;
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec(v_prio_2587_);
lean_dec(v_declName_2586_);
v_a_2603_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2599_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2599_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v_prio_2587_);
lean_dec(v_declName_2586_);
v_a_2611_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2593_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2593_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst___boxed(lean_object* v_declName_2619_, lean_object* v_prio_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_2619_, v_prio_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
return v_res_2626_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0));
v___x_2629_ = l_Lean_stringToMessageData(v___x_2628_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2));
v___x_2632_ = l_Lean_stringToMessageData(v___x_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(lean_object* v_fvar_2633_, lean_object* v_prio_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v___x_2640_; 
lean_inc(v_fvar_2633_);
v___x_2640_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvar_2633_, v_a_2635_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref(v___x_2640_);
if (lean_obj_tag(v_a_2641_) == 1)
{
lean_object* v_val_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2651_; 
v_val_2642_ = lean_ctor_get(v_a_2641_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_a_2641_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2644_ = v_a_2641_;
v_isShared_2645_ = v_isSharedCheck_2651_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_val_2642_);
lean_dec(v_a_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2651_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2646_ = l_Lean_LocalDecl_type(v_val_2642_);
lean_dec(v_val_2642_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v_fvar_2633_);
v___x_2648_ = v___x_2644_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_fvar_2633_);
v___x_2648_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2649_; 
v___x_2649_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v___x_2646_, v___x_2648_, v_prio_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
return v___x_2649_;
}
}
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec(v_a_2641_);
lean_dec(v_prio_2634_);
v___x_2652_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1);
v___x_2653_ = l_Lean_MessageData_ofName(v_fvar_2633_);
v___x_2654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3);
v___x_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2654_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2656_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
return v___x_2657_;
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v_prio_2634_);
lean_dec(v_fvar_2633_);
v_a_2658_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2640_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2640_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___boxed(lean_object* v_fvar_2666_, lean_object* v_prio_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvar_2666_, v_prio_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; lean_object* v_ngen_2677_; lean_object* v_namePrefix_2678_; lean_object* v_idx_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2708_; 
v___x_2676_ = lean_st_ref_get(v___y_2674_);
v_ngen_2677_ = lean_ctor_get(v___x_2676_, 2);
lean_inc_ref(v_ngen_2677_);
lean_dec(v___x_2676_);
v_namePrefix_2678_ = lean_ctor_get(v_ngen_2677_, 0);
v_idx_2679_ = lean_ctor_get(v_ngen_2677_, 1);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_ngen_2677_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2681_ = v_ngen_2677_;
v_isShared_2682_ = v_isSharedCheck_2708_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_idx_2679_);
lean_inc(v_namePrefix_2678_);
lean_dec(v_ngen_2677_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2708_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v_env_2684_; lean_object* v_nextMacroScope_2685_; lean_object* v_auxDeclNGen_2686_; lean_object* v_traceState_2687_; lean_object* v_cache_2688_; lean_object* v_messages_2689_; lean_object* v_infoState_2690_; lean_object* v_snapshotTasks_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2706_; 
v___x_2683_ = lean_st_ref_take(v___y_2674_);
v_env_2684_ = lean_ctor_get(v___x_2683_, 0);
v_nextMacroScope_2685_ = lean_ctor_get(v___x_2683_, 1);
v_auxDeclNGen_2686_ = lean_ctor_get(v___x_2683_, 3);
v_traceState_2687_ = lean_ctor_get(v___x_2683_, 4);
v_cache_2688_ = lean_ctor_get(v___x_2683_, 5);
v_messages_2689_ = lean_ctor_get(v___x_2683_, 6);
v_infoState_2690_ = lean_ctor_get(v___x_2683_, 7);
v_snapshotTasks_2691_ = lean_ctor_get(v___x_2683_, 8);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; 
v_unused_2707_ = lean_ctor_get(v___x_2683_, 2);
lean_dec(v_unused_2707_);
v___x_2693_ = v___x_2683_;
v_isShared_2694_ = v_isSharedCheck_2706_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_snapshotTasks_2691_);
lean_inc(v_infoState_2690_);
lean_inc(v_messages_2689_);
lean_inc(v_cache_2688_);
lean_inc(v_traceState_2687_);
lean_inc(v_auxDeclNGen_2686_);
lean_inc(v_nextMacroScope_2685_);
lean_inc(v_env_2684_);
lean_dec(v___x_2683_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2706_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_r_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
lean_inc(v_idx_2679_);
lean_inc(v_namePrefix_2678_);
v_r_2695_ = l_Lean_Name_num___override(v_namePrefix_2678_, v_idx_2679_);
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_add(v_idx_2679_, v___x_2696_);
lean_dec(v_idx_2679_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 1, v___x_2697_);
v___x_2699_ = v___x_2681_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_namePrefix_2678_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2701_; 
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 2, v___x_2699_);
v___x_2701_ = v___x_2693_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_env_2684_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_nextMacroScope_2685_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v_auxDeclNGen_2686_);
lean_ctor_set(v_reuseFailAlloc_2704_, 4, v_traceState_2687_);
lean_ctor_set(v_reuseFailAlloc_2704_, 5, v_cache_2688_);
lean_ctor_set(v_reuseFailAlloc_2704_, 6, v_messages_2689_);
lean_ctor_set(v_reuseFailAlloc_2704_, 7, v_infoState_2690_);
lean_ctor_set(v_reuseFailAlloc_2704_, 8, v_snapshotTasks_2691_);
v___x_2701_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_st_ref_set(v___y_2674_, v___x_2701_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_r_2695_);
return v___x_2703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg___boxed(lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_2709_);
lean_dec(v___y_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___boxed(lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(lean_object* v_ref_2724_, lean_object* v_proof_2725_, lean_object* v_prio_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v___x_2732_; 
lean_inc(v_a_2730_);
lean_inc_ref(v_a_2729_);
lean_inc(v_a_2728_);
lean_inc_ref(v_a_2727_);
lean_inc_ref(v_proof_2725_);
v___x_2732_ = lean_infer_type(v_proof_2725_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; lean_object* v_a_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref(v___x_2732_);
v___x_2734_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v_a_2730_);
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref(v___x_2734_);
v___x_2736_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2736_, 0, v_a_2735_);
lean_ctor_set(v___x_2736_, 1, v_ref_2724_);
lean_ctor_set(v___x_2736_, 2, v_proof_2725_);
v___x_2737_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_2733_, v___x_2736_, v_prio_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
return v___x_2737_;
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_prio_2726_);
lean_dec_ref(v_proof_2725_);
lean_dec(v_ref_2724_);
v_a_2738_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2732_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2732_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx___boxed(lean_object* v_ref_2746_, lean_object* v_proof_2747_, lean_object* v_prio_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(v_ref_2746_, v_proof_2747_, v_prio_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
return v_res_2754_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2755_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0);
v___x_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
return v___x_2759_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
v___x_2761_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
lean_ctor_set(v___x_2761_, 2, v___x_2760_);
lean_ctor_set(v___x_2761_, 3, v___x_2760_);
lean_ctor_set(v___x_2761_, 4, v___x_2760_);
lean_ctor_set(v___x_2761_, 5, v___x_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(lean_object* v_ext_2762_, lean_object* v_b_2763_, uint8_t v_kind_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_currNamespace_2769_; lean_object* v___x_2770_; lean_object* v_env_2771_; lean_object* v_nextMacroScope_2772_; lean_object* v_ngen_2773_; lean_object* v_auxDeclNGen_2774_; lean_object* v_traceState_2775_; lean_object* v_messages_2776_; lean_object* v_infoState_2777_; lean_object* v_snapshotTasks_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2805_; 
v_currNamespace_2769_ = lean_ctor_get(v___y_2766_, 6);
v___x_2770_ = lean_st_ref_take(v___y_2767_);
v_env_2771_ = lean_ctor_get(v___x_2770_, 0);
v_nextMacroScope_2772_ = lean_ctor_get(v___x_2770_, 1);
v_ngen_2773_ = lean_ctor_get(v___x_2770_, 2);
v_auxDeclNGen_2774_ = lean_ctor_get(v___x_2770_, 3);
v_traceState_2775_ = lean_ctor_get(v___x_2770_, 4);
v_messages_2776_ = lean_ctor_get(v___x_2770_, 6);
v_infoState_2777_ = lean_ctor_get(v___x_2770_, 7);
v_snapshotTasks_2778_ = lean_ctor_get(v___x_2770_, 8);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; 
v_unused_2806_ = lean_ctor_get(v___x_2770_, 5);
lean_dec(v_unused_2806_);
v___x_2780_ = v___x_2770_;
v_isShared_2781_ = v_isSharedCheck_2805_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_snapshotTasks_2778_);
lean_inc(v_infoState_2777_);
lean_inc(v_messages_2776_);
lean_inc(v_traceState_2775_);
lean_inc(v_auxDeclNGen_2774_);
lean_inc(v_ngen_2773_);
lean_inc(v_nextMacroScope_2772_);
lean_inc(v_env_2771_);
lean_dec(v___x_2770_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2805_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
lean_inc(v_currNamespace_2769_);
v___x_2782_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2771_, v_ext_2762_, v_b_2763_, v_kind_2764_, v_currNamespace_2769_);
v___x_2783_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 5, v___x_2783_);
lean_ctor_set(v___x_2780_, 0, v___x_2782_);
v___x_2785_ = v___x_2780_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_nextMacroScope_2772_);
lean_ctor_set(v_reuseFailAlloc_2804_, 2, v_ngen_2773_);
lean_ctor_set(v_reuseFailAlloc_2804_, 3, v_auxDeclNGen_2774_);
lean_ctor_set(v_reuseFailAlloc_2804_, 4, v_traceState_2775_);
lean_ctor_set(v_reuseFailAlloc_2804_, 5, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2804_, 6, v_messages_2776_);
lean_ctor_set(v_reuseFailAlloc_2804_, 7, v_infoState_2777_);
lean_ctor_set(v_reuseFailAlloc_2804_, 8, v_snapshotTasks_2778_);
v___x_2785_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v_mctx_2788_; lean_object* v_zetaDeltaFVarIds_2789_; lean_object* v_postponed_2790_; lean_object* v_diag_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2802_; 
v___x_2786_ = lean_st_ref_set(v___y_2767_, v___x_2785_);
v___x_2787_ = lean_st_ref_take(v___y_2765_);
v_mctx_2788_ = lean_ctor_get(v___x_2787_, 0);
v_zetaDeltaFVarIds_2789_ = lean_ctor_get(v___x_2787_, 2);
v_postponed_2790_ = lean_ctor_get(v___x_2787_, 3);
v_diag_2791_ = lean_ctor_get(v___x_2787_, 4);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v___x_2787_, 1);
lean_dec(v_unused_2803_);
v___x_2793_ = v___x_2787_;
v_isShared_2794_ = v_isSharedCheck_2802_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_diag_2791_);
lean_inc(v_postponed_2790_);
lean_inc(v_zetaDeltaFVarIds_2789_);
lean_inc(v_mctx_2788_);
lean_dec(v___x_2787_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2802_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2795_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 1, v___x_2795_);
v___x_2797_ = v___x_2793_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_mctx_2788_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v_zetaDeltaFVarIds_2789_);
lean_ctor_set(v_reuseFailAlloc_2801_, 3, v_postponed_2790_);
lean_ctor_set(v_reuseFailAlloc_2801_, 4, v_diag_2791_);
v___x_2797_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2798_ = lean_st_ref_set(v___y_2765_, v___x_2797_);
v___x_2799_ = lean_box(0);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___boxed(lean_object* v_ext_2807_, lean_object* v_b_2808_, lean_object* v_kind_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
uint8_t v_kind_boxed_2814_; lean_object* v_res_2815_; 
v_kind_boxed_2814_ = lean_unbox(v_kind_2809_);
v_res_2815_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2807_, v_b_2808_, v_kind_boxed_2814_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(lean_object* v_00_u03b1_2816_, lean_object* v_00_u03b2_2817_, lean_object* v_00_u03c3_2818_, lean_object* v_ext_2819_, lean_object* v_b_2820_, uint8_t v_kind_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2819_, v_b_2820_, v_kind_2821_, v___y_2823_, v___y_2824_, v___y_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_00_u03b2_2829_, lean_object* v_00_u03c3_2830_, lean_object* v_ext_2831_, lean_object* v_b_2832_, lean_object* v_kind_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
uint8_t v_kind_boxed_2839_; lean_object* v_res_2840_; 
v_kind_boxed_2839_ = lean_unbox(v_kind_2833_);
v_res_2840_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(v_00_u03b1_2828_, v_00_u03b2_2829_, v_00_u03c3_2830_, v_ext_2831_, v_b_2832_, v_kind_boxed_2839_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(lean_object* v_ext_2841_, lean_object* v_declName_2842_, lean_object* v_prio_2843_, uint8_t v_attrKind_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_2842_, v_prio_2843_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref(v___x_2850_);
v___x_2852_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2841_, v_a_2851_, v_attrKind_2844_, v_a_2846_, v_a_2847_, v_a_2848_);
return v___x_2852_;
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec_ref(v_ext_2841_);
v_a_2853_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2850_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2850_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst___boxed(lean_object* v_ext_2861_, lean_object* v_declName_2862_, lean_object* v_prio_2863_, lean_object* v_attrKind_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
uint8_t v_attrKind_boxed_2870_; lean_object* v_res_2871_; 
v_attrKind_boxed_2870_ = lean_unbox(v_attrKind_2864_);
v_res_2871_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(v_ext_2861_, v_declName_2862_, v_prio_2863_, v_attrKind_boxed_2870_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(lean_object* v_ext_2872_, lean_object* v_fvar_2873_, lean_object* v_prio_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvar_2873_, v_prio_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2880_);
v___x_2882_ = 1;
v___x_2883_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2872_, v_a_2881_, v___x_2882_, v_a_2876_, v_a_2877_, v_a_2878_);
return v___x_2883_;
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec_ref(v_ext_2872_);
v_a_2884_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2880_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2880_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal___boxed(lean_object* v_ext_2892_, lean_object* v_fvar_2893_, lean_object* v_prio_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(v_ext_2892_, v_fvar_2893_, v_prio_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(uint8_t v_x_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___y_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed(lean_object* v_x_2904_, lean_object* v___y_2905_){
_start:
{
uint8_t v_x_31__boxed_2906_; lean_object* v_res_2907_; 
v_x_31__boxed_2906_ = lean_unbox(v_x_2904_);
v_res_2907_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(v_x_31__boxed_2906_, v___y_2905_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(lean_object* v___y_2908_){
_start:
{
lean_inc_ref(v___y_2908_);
return v___y_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed(lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(v___y_2909_);
lean_dec_ref(v___y_2909_);
return v_res_2910_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5(void){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2917_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__6(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2918_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2);
v___x_2919_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
lean_ctor_set(v___x_2920_, 1, v___x_2918_);
return v___x_2920_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__7(void){
_start:
{
lean_object* v___f_2921_; lean_object* v___f_2922_; lean_object* v___x_2923_; lean_object* v___f_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___f_2921_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1));
v___f_2922_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2));
v___x_2923_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__6, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__6_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__6);
v___f_2924_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0));
v___x_2925_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4));
v___x_2926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v___f_2924_);
lean_ctor_set(v___x_2926_, 2, v___x_2923_);
lean_ctor_set(v___x_2926_, 3, v___f_2922_);
lean_ctor_set(v___x_2926_, 4, v___f_2921_);
return v___x_2926_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt(void){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__7, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__7_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__7);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt;
v___x_2930_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2____boxed(lean_object* v_a_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
return v_res_2932_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0));
v___x_2935_ = l_Lean_stringToMessageData(v___x_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(lean_object* v_____r_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1);
v___x_2943_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2942_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed(lean_object* v_____r_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(v_____r_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
return v_res_2950_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2951_; double v___x_2952_; 
v___x_2951_ = lean_unsigned_to_nat(0u);
v___x_2952_ = lean_float_of_nat(v___x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(lean_object* v_cls_2956_, lean_object* v_msg_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_ref_2963_; lean_object* v___x_2964_; lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3009_; 
v_ref_2963_ = lean_ctor_get(v___y_2960_, 5);
v___x_2964_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_3009_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3009_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v_traceState_2970_; lean_object* v_env_2971_; lean_object* v_nextMacroScope_2972_; lean_object* v_ngen_2973_; lean_object* v_auxDeclNGen_2974_; lean_object* v_cache_2975_; lean_object* v_messages_2976_; lean_object* v_infoState_2977_; lean_object* v_snapshotTasks_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3008_; 
v___x_2969_ = lean_st_ref_take(v___y_2961_);
v_traceState_2970_ = lean_ctor_get(v___x_2969_, 4);
v_env_2971_ = lean_ctor_get(v___x_2969_, 0);
v_nextMacroScope_2972_ = lean_ctor_get(v___x_2969_, 1);
v_ngen_2973_ = lean_ctor_get(v___x_2969_, 2);
v_auxDeclNGen_2974_ = lean_ctor_get(v___x_2969_, 3);
v_cache_2975_ = lean_ctor_get(v___x_2969_, 5);
v_messages_2976_ = lean_ctor_get(v___x_2969_, 6);
v_infoState_2977_ = lean_ctor_get(v___x_2969_, 7);
v_snapshotTasks_2978_ = lean_ctor_get(v___x_2969_, 8);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2980_ = v___x_2969_;
v_isShared_2981_ = v_isSharedCheck_3008_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_snapshotTasks_2978_);
lean_inc(v_infoState_2977_);
lean_inc(v_messages_2976_);
lean_inc(v_cache_2975_);
lean_inc(v_traceState_2970_);
lean_inc(v_auxDeclNGen_2974_);
lean_inc(v_ngen_2973_);
lean_inc(v_nextMacroScope_2972_);
lean_inc(v_env_2971_);
lean_dec(v___x_2969_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3008_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
uint64_t v_tid_2982_; lean_object* v_traces_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3007_; 
v_tid_2982_ = lean_ctor_get_uint64(v_traceState_2970_, sizeof(void*)*1);
v_traces_2983_ = lean_ctor_get(v_traceState_2970_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_traceState_2970_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2985_ = v_traceState_2970_;
v_isShared_2986_ = v_isSharedCheck_3007_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_traces_2983_);
lean_dec(v_traceState_2970_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3007_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; double v___x_2988_; uint8_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2987_ = lean_box(0);
v___x_2988_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0);
v___x_2989_ = 0;
v___x_2990_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1));
v___x_2991_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2991_, 0, v_cls_2956_);
lean_ctor_set(v___x_2991_, 1, v___x_2987_);
lean_ctor_set(v___x_2991_, 2, v___x_2990_);
lean_ctor_set_float(v___x_2991_, sizeof(void*)*3, v___x_2988_);
lean_ctor_set_float(v___x_2991_, sizeof(void*)*3 + 8, v___x_2988_);
lean_ctor_set_uint8(v___x_2991_, sizeof(void*)*3 + 16, v___x_2989_);
v___x_2992_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2));
v___x_2993_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2991_);
lean_ctor_set(v___x_2993_, 1, v_a_2965_);
lean_ctor_set(v___x_2993_, 2, v___x_2992_);
lean_inc(v_ref_2963_);
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v_ref_2963_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = l_Lean_PersistentArray_push___redArg(v_traces_2983_, v___x_2994_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2995_);
v___x_2997_ = v___x_2985_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2995_);
lean_ctor_set_uint64(v_reuseFailAlloc_3006_, sizeof(void*)*1, v_tid_2982_);
v___x_2997_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2999_; 
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 4, v___x_2997_);
v___x_2999_ = v___x_2980_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_env_2971_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_nextMacroScope_2972_);
lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_ngen_2973_);
lean_ctor_set(v_reuseFailAlloc_3005_, 3, v_auxDeclNGen_2974_);
lean_ctor_set(v_reuseFailAlloc_3005_, 4, v___x_2997_);
lean_ctor_set(v_reuseFailAlloc_3005_, 5, v_cache_2975_);
lean_ctor_set(v_reuseFailAlloc_3005_, 6, v_messages_2976_);
lean_ctor_set(v_reuseFailAlloc_3005_, 7, v_infoState_2977_);
lean_ctor_set(v_reuseFailAlloc_3005_, 8, v_snapshotTasks_2978_);
v___x_2999_ = v_reuseFailAlloc_3005_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_3000_ = lean_st_ref_set(v___y_2961_, v___x_2999_);
v___x_3001_ = lean_box(0);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_3001_);
v___x_3003_ = v___x_2967_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___boxed(lean_object* v_cls_3010_, lean_object* v_msg_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v_cls_3010_, v_msg_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(lean_object* v_constName_3018_, uint8_t v_skipRealize_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v___x_3025_; lean_object* v_env_3026_; lean_object* v___x_3027_; 
v___x_3025_ = lean_st_ref_get(v___y_3023_);
v_env_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc_ref(v_env_3026_);
lean_dec(v___x_3025_);
lean_inc(v_constName_3018_);
v___x_3027_ = l_Lean_Environment_findAsync_x3f(v_env_3026_, v_constName_3018_, v_skipRealize_3019_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_3018_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
return v___x_3028_;
}
else
{
lean_object* v_val_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec(v_constName_3018_);
v_val_3029_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3027_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_val_3029_);
lean_dec(v___x_3027_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set_tag(v___x_3031_, 0);
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_val_3029_);
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
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0___boxed(lean_object* v_constName_3037_, lean_object* v_skipRealize_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
uint8_t v_skipRealize_boxed_3044_; lean_object* v_res_3045_; 
v_skipRealize_boxed_3044_ = lean_unbox(v_skipRealize_3038_);
v_res_3045_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_constName_3037_, v_skipRealize_boxed_3044_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
return v_res_3045_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3052_; uint64_t v___x_3053_; 
v___x_3052_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0));
v___x_3053_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3052_);
return v___x_3053_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1);
v___x_3055_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0));
v___x_3056_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set_uint64(v___x_3056_, sizeof(void*)*1, v___x_3054_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3057_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3);
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
return v___x_3059_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3060_ = lean_box(1);
v___x_3061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_3062_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v___x_3061_);
lean_ctor_set(v___x_3063_, 2, v___x_3060_);
return v___x_3063_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3067_ = lean_unsigned_to_nat(0u);
v___x_3068_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
lean_ctor_set(v___x_3068_, 2, v___x_3067_);
lean_ctor_set(v___x_3068_, 3, v___x_3066_);
lean_ctor_set(v___x_3068_, 4, v___x_3066_);
lean_ctor_set(v___x_3068_, 5, v___x_3066_);
lean_ctor_set(v___x_3068_, 6, v___x_3066_);
lean_ctor_set(v___x_3068_, 7, v___x_3066_);
lean_ctor_set(v___x_3068_, 8, v___x_3066_);
return v___x_3068_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3070_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
lean_ctor_set(v___x_3070_, 2, v___x_3069_);
lean_ctor_set(v___x_3070_, 3, v___x_3069_);
lean_ctor_set(v___x_3070_, 4, v___x_3069_);
lean_ctor_set(v___x_3070_, 5, v___x_3069_);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
lean_ctor_set(v___x_3072_, 2, v___x_3071_);
lean_ctor_set(v___x_3072_, 3, v___x_3071_);
lean_ctor_set(v___x_3072_, 4, v___x_3071_);
return v___x_3072_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12));
v___x_3078_ = l_Lean_stringToMessageData(v___x_3077_);
return v___x_3078_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_3080_ = l_String_toRawSubstring_x27(v___x_3079_);
return v___x_3080_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17(void){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Array_mkArray0(lean_box(0));
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(lean_object* v___x_3087_, lean_object* v_ext_3088_, lean_object* v___f_3089_, lean_object* v___x_3090_, lean_object* v___x_3091_, lean_object* v___x_3092_, lean_object* v___x_3093_, lean_object* v_declName_3094_, lean_object* v_stx_3095_, uint8_t v_attrKind_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
uint8_t v___x_3100_; uint8_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3100_ = 0;
v___x_3101_ = 1;
v___x_3102_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2);
v___x_3103_ = lean_unsigned_to_nat(0u);
v___x_3104_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_3105_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5);
v___x_3106_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6));
v___x_3107_ = lean_box(0);
lean_inc(v___x_3087_);
v___x_3108_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3108_, 0, v___x_3102_);
lean_ctor_set(v___x_3108_, 1, v___x_3087_);
lean_ctor_set(v___x_3108_, 2, v___x_3105_);
lean_ctor_set(v___x_3108_, 3, v___x_3106_);
lean_ctor_set(v___x_3108_, 4, v___x_3107_);
lean_ctor_set(v___x_3108_, 5, v___x_3103_);
lean_ctor_set(v___x_3108_, 6, v___x_3107_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*7, v___x_3100_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*7 + 1, v___x_3100_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*7 + 2, v___x_3100_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*7 + 3, v___x_3101_);
v___x_3109_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7);
v___x_3110_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8);
v___x_3111_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9);
v___x_3112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3109_);
lean_ctor_set(v___x_3112_, 1, v___x_3110_);
lean_ctor_set(v___x_3112_, 2, v___x_3087_);
lean_ctor_set(v___x_3112_, 3, v___x_3104_);
lean_ctor_set(v___x_3112_, 4, v___x_3111_);
v___x_3113_ = lean_st_mk_ref(v___x_3112_);
lean_inc(v_declName_3094_);
v___x_3114_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_declName_3094_, v___x_3100_, v___x_3108_, v___x_3113_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec_ref(v___x_3114_);
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = l_Lean_Syntax_getArg(v_stx_3095_, v___x_3115_);
lean_inc(v___x_3116_);
v___x_3117_ = l_Lean_getAttrParamOptPrio(v___x_3116_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3213_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3213_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3213_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___y_3129_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; uint8_t v___y_3137_; lean_object* v___x_3150_; 
v___x_3122_ = lean_box(0);
lean_inc(v_declName_3094_);
v___x_3150_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(v_ext_3088_, v_declName_3094_, v_a_3118_, v_attrKind_3096_, v___x_3108_, v___x_3113_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_dec(v___x_3116_);
lean_dec_ref(v___x_3108_);
lean_dec(v_declName_3094_);
lean_dec_ref(v___x_3093_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v___x_3090_);
lean_dec_ref(v___f_3089_);
v___y_3129_ = v___x_3150_;
goto v___jp_3128_;
}
else
{
lean_object* v_a_3151_; uint8_t v___y_3153_; uint8_t v___x_3211_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
v___x_3211_ = l_Lean_Exception_isInterrupt(v_a_3151_);
if (v___x_3211_ == 0)
{
uint8_t v___x_3212_; 
v___x_3212_ = l_Lean_Exception_isRuntime(v_a_3151_);
v___y_3153_ = v___x_3212_;
goto v___jp_3152_;
}
else
{
lean_dec(v_a_3151_);
v___y_3153_ = v___x_3211_;
goto v___jp_3152_;
}
v___jp_3152_:
{
if (v___y_3153_ == 0)
{
lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3209_; 
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v___x_3150_, 0);
lean_dec(v_unused_3210_);
v___x_3155_ = v___x_3150_;
v_isShared_3156_ = v_isSharedCheck_3209_;
goto v_resetjp_3154_;
}
else
{
lean_dec(v___x_3150_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3209_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_3158_ = l_Lean_getBuiltinAttributeImpl(v___x_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v_options_3160_; lean_object* v_ref_3161_; lean_object* v_quotContext_3162_; lean_object* v_currMacroScope_3163_; lean_object* v_inheritedTraceOptions_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v_add_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3191_; 
lean_del_object(v___x_3155_);
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref(v___x_3158_);
v_options_3160_ = lean_ctor_get(v___y_3097_, 2);
v_ref_3161_ = lean_ctor_get(v___y_3097_, 5);
v_quotContext_3162_ = lean_ctor_get(v___y_3097_, 10);
v_currMacroScope_3163_ = lean_ctor_get(v___y_3097_, 11);
v_inheritedTraceOptions_3164_ = lean_ctor_get(v___y_3097_, 13);
v___x_3165_ = l_Lean_SourceInfo_fromRef(v_ref_3161_, v___y_3153_);
v___x_3166_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14);
lean_inc(v_currMacroScope_3163_);
lean_inc(v_quotContext_3162_);
v___x_3167_ = l_Lean_addMacroScope(v_quotContext_3162_, v___x_3157_, v_currMacroScope_3163_);
v___x_3168_ = lean_box(0);
lean_inc(v___x_3165_);
v___x_3169_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3165_);
lean_ctor_set(v___x_3169_, 1, v___x_3166_);
lean_ctor_set(v___x_3169_, 2, v___x_3167_);
lean_ctor_set(v___x_3169_, 3, v___x_3168_);
v_add_3170_ = lean_ctor_get(v_a_3159_, 1);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_a_3159_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; lean_object* v_unused_3193_; 
v_unused_3192_ = lean_ctor_get(v_a_3159_, 2);
lean_dec(v_unused_3192_);
v_unused_3193_ = lean_ctor_get(v_a_3159_, 0);
lean_dec(v_unused_3193_);
v___x_3172_ = v_a_3159_;
v_isShared_3173_ = v_isSharedCheck_3191_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_add_3170_);
lean_dec(v_a_3159_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3191_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3177_; 
v___x_3174_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16));
v___x_3175_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17);
lean_inc(v___x_3165_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set_tag(v___x_3172_, 1);
lean_ctor_set(v___x_3172_, 2, v___x_3175_);
lean_ctor_set(v___x_3172_, 1, v___x_3174_);
lean_ctor_set(v___x_3172_, 0, v___x_3165_);
v___x_3177_ = v___x_3172_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3190_, 2, v___x_3175_);
v___x_3177_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3178_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18));
v___x_3179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3180_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19));
v___x_3181_ = l_Lean_Name_mkStr4(v___x_3093_, v___x_3178_, v___x_3179_, v___x_3180_);
v___x_3182_ = l_Lean_Syntax_node2(v___x_3165_, v___x_3181_, v___x_3169_, v___x_3177_);
v___x_3183_ = lean_unsigned_to_nat(3u);
v___x_3184_ = l_Lean_Syntax_setArg(v___x_3182_, v___x_3183_, v___x_3116_);
v___x_3185_ = lean_box(v_attrKind_3096_);
lean_inc(v___y_3098_);
lean_inc_ref(v___y_3097_);
v___x_3186_ = lean_apply_6(v_add_3170_, v_declName_3094_, v___x_3184_, v___x_3185_, v___y_3097_, v___y_3098_, lean_box(0));
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_dec_ref(v___x_3186_);
lean_dec_ref(v___x_3108_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v___x_3090_);
lean_dec_ref(v___f_3089_);
goto v___jp_3123_;
}
else
{
lean_object* v_a_3187_; uint8_t v___x_3188_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
v___x_3188_ = l_Lean_Exception_isInterrupt(v_a_3187_);
if (v___x_3188_ == 0)
{
uint8_t v___x_3189_; 
lean_inc(v_a_3187_);
v___x_3189_ = l_Lean_Exception_isRuntime(v_a_3187_);
v___y_3133_ = v_a_3187_;
v___y_3134_ = v___x_3186_;
v___y_3135_ = v_inheritedTraceOptions_3164_;
v___y_3136_ = v_options_3160_;
v___y_3137_ = v___x_3189_;
goto v___jp_3132_;
}
else
{
v___y_3133_ = v_a_3187_;
v___y_3134_ = v___x_3186_;
v___y_3135_ = v_inheritedTraceOptions_3164_;
v___y_3136_ = v_options_3160_;
v___y_3137_ = v___x_3188_;
goto v___jp_3132_;
}
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3208_; 
lean_del_object(v___x_3120_);
lean_dec(v___x_3116_);
lean_dec(v___x_3113_);
lean_dec_ref(v___x_3108_);
lean_dec(v_declName_3094_);
lean_dec_ref(v___x_3093_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v___x_3090_);
lean_dec_ref(v___f_3089_);
v_a_3194_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3196_ = v___x_3158_;
v_isShared_3197_ = v_isSharedCheck_3208_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3158_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3208_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v_ref_3198_; lean_object* v___x_3199_; lean_object* v___x_3201_; 
v_ref_3198_ = lean_ctor_get(v___y_3097_, 5);
v___x_3199_ = lean_io_error_to_string(v_a_3194_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 3);
lean_ctor_set(v___x_3155_, 0, v___x_3199_);
v___x_3201_ = v___x_3155_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3202_ = l_Lean_MessageData_ofFormat(v___x_3201_);
lean_inc(v_ref_3198_);
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v_ref_3198_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3203_);
v___x_3205_ = v___x_3196_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3116_);
lean_dec_ref(v___x_3108_);
lean_dec(v_declName_3094_);
lean_dec_ref(v___x_3093_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v___x_3090_);
lean_dec_ref(v___f_3089_);
v___y_3129_ = v___x_3150_;
goto v___jp_3128_;
}
}
}
v___jp_3123_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3124_ = lean_st_ref_get(v___x_3113_);
lean_dec(v___x_3113_);
lean_dec(v___x_3124_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v___x_3122_);
v___x_3126_ = v___x_3120_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3122_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
v___jp_3128_:
{
if (lean_obj_tag(v___y_3129_) == 0)
{
lean_dec_ref(v___y_3129_);
goto v___jp_3123_;
}
else
{
lean_del_object(v___x_3120_);
lean_dec(v___x_3113_);
return v___y_3129_;
}
}
v___jp_3130_:
{
lean_object* v___x_3131_; 
lean_inc(v___y_3098_);
lean_inc_ref(v___y_3097_);
lean_inc(v___x_3113_);
v___x_3131_ = lean_apply_6(v___f_3089_, v___x_3122_, v___x_3108_, v___x_3113_, v___y_3097_, v___y_3098_, lean_box(0));
v___y_3129_ = v___x_3131_;
goto v___jp_3128_;
}
v___jp_3132_:
{
if (v___y_3137_ == 0)
{
uint8_t v_hasTrace_3138_; 
lean_dec_ref(v___y_3134_);
v_hasTrace_3138_ = lean_ctor_get_uint8(v___y_3136_, sizeof(void*)*1);
if (v_hasTrace_3138_ == 0)
{
lean_dec_ref(v___y_3133_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v___x_3090_);
goto v___jp_3130_;
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3140_ = l_Lean_Name_mkStr4(v___x_3090_, v___x_3091_, v___x_3092_, v___x_3139_);
v___x_3141_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11));
lean_inc(v___x_3140_);
v___x_3142_ = l_Lean_Name_append(v___x_3141_, v___x_3140_);
v___x_3143_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_3135_, v___y_3136_, v___x_3142_);
lean_dec(v___x_3142_);
if (v___x_3143_ == 0)
{
lean_dec(v___x_3140_);
lean_dec_ref(v___y_3133_);
goto v___jp_3130_;
}
else
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3144_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13);
v___x_3145_ = l_Lean_Exception_toMessageData(v___y_3133_);
v___x_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v___x_3140_, v___x_3146_, v___x_3108_, v___x_3113_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3149_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref(v___x_3147_);
lean_inc(v___y_3098_);
lean_inc_ref(v___y_3097_);
lean_inc(v___x_3113_);
v___x_3149_ = lean_apply_6(v___f_3089_, v_a_3148_, v___x_3108_, v___x_3113_, v___y_3097_, v___y_3098_, lean_box(0));
v___y_3129_ = v___x_3149_;
goto v___jp_3128_;
}
else
{
lean_dec_ref(v___x_3108_);
lean_dec_ref(v___f_3089_);
v___y_3129_ = v___x_3147_;
goto v___jp_3128_;
}
}
}
}
else
{
lean_dec_ref(v___y_3133_);
lean_del_object(v___x_3120_);
lean_dec(v___x_3113_);
lean_dec_ref(v___x_3108_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v___x_3090_);
lean_dec_ref(v___f_3089_);
return v___y_3134_;
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec(v___x_3116_);
lean_dec(v___x_3113_);
lean_dec_ref(v___x_3108_);
lean_dec(v_declName_3094_);
lean_dec_ref(v___x_3093_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v___x_3090_);
lean_dec_ref(v___f_3089_);
lean_dec_ref(v_ext_3088_);
v_a_3214_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3117_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3117_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec(v___x_3113_);
lean_dec_ref(v___x_3108_);
lean_dec(v_declName_3094_);
lean_dec_ref(v___x_3093_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v___x_3090_);
lean_dec_ref(v___f_3089_);
lean_dec_ref(v_ext_3088_);
v_a_3222_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3114_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3114_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed(lean_object* v___x_3230_, lean_object* v_ext_3231_, lean_object* v___f_3232_, lean_object* v___x_3233_, lean_object* v___x_3234_, lean_object* v___x_3235_, lean_object* v___x_3236_, lean_object* v_declName_3237_, lean_object* v_stx_3238_, lean_object* v_attrKind_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
uint8_t v_attrKind_boxed_3243_; lean_object* v_res_3244_; 
v_attrKind_boxed_3243_ = lean_unbox(v_attrKind_3239_);
v_res_3244_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(v___x_3230_, v_ext_3231_, v___f_3232_, v___x_3233_, v___x_3234_, v___x_3235_, v___x_3236_, v_declName_3237_, v_stx_3238_, v_attrKind_boxed_3243_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v_stx_3238_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(lean_object* v_msgData_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; lean_object* v_env_3250_; lean_object* v_options_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3249_ = lean_st_ref_get(v___y_3247_);
v_env_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc_ref(v_env_3250_);
lean_dec(v___x_3249_);
v_options_3251_ = lean_ctor_get(v___y_3246_, 2);
v___x_3252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_3253_ = lean_unsigned_to_nat(32u);
v___x_3254_ = lean_mk_empty_array_with_capacity(v___x_3253_);
lean_dec_ref(v___x_3254_);
v___x_3255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
lean_inc_ref(v_options_3251_);
v___x_3256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3256_, 0, v_env_3250_);
lean_ctor_set(v___x_3256_, 1, v___x_3252_);
lean_ctor_set(v___x_3256_, 2, v___x_3255_);
lean_ctor_set(v___x_3256_, 3, v_options_3251_);
v___x_3257_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set(v___x_3257_, 1, v_msgData_3245_);
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2___boxed(lean_object* v_msgData_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msgData_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(lean_object* v_msg_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_ref_3268_; lean_object* v___x_3269_; lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3278_; 
v_ref_3268_ = lean_ctor_get(v___y_3265_, 5);
v___x_3269_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msg_3264_, v___y_3265_, v___y_3266_);
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_inc(v_ref_3268_);
v___x_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3274_, 0, v_ref_3268_);
lean_ctor_set(v___x_3274_, 1, v_a_3270_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set_tag(v___x_3272_, 1);
lean_ctor_set(v___x_3272_, 0, v___x_3274_);
v___x_3276_ = v___x_3272_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg___boxed(lean_object* v_msg_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v_msg_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
return v_res_3283_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0));
v___x_3286_ = l_Lean_stringToMessageData(v___x_3285_);
return v___x_3286_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2));
v___x_3289_ = l_Lean_stringToMessageData(v___x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(lean_object* v___x_3290_, lean_object* v_decl_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3295_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1);
v___x_3296_ = l_Lean_MessageData_ofName(v___x_3290_);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v___x_3299_, v___y_3292_, v___y_3293_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed(lean_object* v___x_3301_, lean_object* v_decl_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(v___x_3301_, v_decl_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v_decl_3302_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(lean_object* v_ext_3327_){
_start:
{
lean_object* v___f_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___f_3334_; lean_object* v___f_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___f_3328_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0));
v___x_3329_ = lean_box(1);
v___x_3330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___f_3334_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3334_, 0, v___x_3329_);
lean_closure_set(v___f_3334_, 1, v_ext_3327_);
lean_closure_set(v___f_3334_, 2, v___f_3328_);
lean_closure_set(v___f_3334_, 3, v___x_3331_);
lean_closure_set(v___f_3334_, 4, v___x_3332_);
lean_closure_set(v___f_3334_, 5, v___x_3333_);
lean_closure_set(v___f_3334_, 6, v___x_3330_);
v___f_3335_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5));
v___x_3336_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7));
v___x_3337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
lean_ctor_set(v___x_3337_, 1, v___f_3334_);
lean_ctor_set(v___x_3337_, 2, v___f_3335_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(lean_object* v_00_u03b1_3338_, lean_object* v_msg_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v_msg_3339_, v___y_3340_, v___y_3341_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___boxed(lean_object* v_00_u03b1_3344_, lean_object* v_msg_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(v_00_u03b1_3344_, v_msg_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
return v_res_3349_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
v___x_3351_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_);
v___x_3354_ = l_Lean_registerBuiltinAttribute(v___x_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2____boxed(lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(lean_object* v_ext_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v_ext_3361_; lean_object* v_toEnvExtension_3362_; lean_object* v_env_3363_; lean_object* v_asyncMode_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3360_ = lean_st_ref_get(v_a_3358_);
v_ext_3361_ = lean_ctor_get(v_ext_3357_, 1);
v_toEnvExtension_3362_ = lean_ctor_get(v_ext_3361_, 0);
v_env_3363_ = lean_ctor_get(v___x_3360_, 0);
lean_inc_ref(v_env_3363_);
lean_dec(v___x_3360_);
v_asyncMode_3364_ = lean_ctor_get(v_toEnvExtension_3362_, 2);
v___x_3365_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
v___x_3366_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3365_, v_ext_3357_, v_env_3363_, v_asyncMode_3364_);
v___x_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg___boxed(lean_object* v_ext_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_3368_, v_a_3369_);
lean_dec(v_a_3369_);
lean_dec_ref(v_ext_3368_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(lean_object* v_ext_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_3372_, v_a_3374_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___boxed(lean_object* v_ext_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(v_ext_3377_, v_a_3378_, v_a_3379_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec_ref(v_ext_3377_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(lean_object* v_a_3382_){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
v___x_3385_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v___x_3384_, v_a_3382_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg___boxed(lean_object* v_a_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3386_);
lean_dec(v_a_3386_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3390_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___boxed(lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(v_a_3393_, v_a_3394_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(lean_object* v_x_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_box(0);
v___x_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object* v_x_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(v_x_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v_x_3403_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___f_3422_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3423_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3424_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3425_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_3426_ = 0;
v___x_3427_ = lean_box(2);
v___x_3428_ = l_Lean_registerTagAttribute(v___x_3423_, v___x_3424_, v___f_3422_, v___x_3425_, v___x_3426_, v___x_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object* v_a_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
return v_res_3430_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(lean_object* v_env_3431_, lean_object* v_ty_3432_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_Expr_getAppFn(v_ty_3432_);
if (lean_obj_tag(v___x_3433_) == 4)
{
lean_object* v_declName_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v_declName_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_declName_3434_);
lean_dec_ref(v___x_3433_);
v___x_3435_ = l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr;
v___x_3436_ = l_Lean_TagAttribute_hasTag(v___x_3435_, v_env_3431_, v_declName_3434_);
return v___x_3436_;
}
else
{
uint8_t v___x_3437_; 
lean_dec_ref(v___x_3433_);
lean_dec_ref(v_env_3431_);
v___x_3437_ = 0;
return v___x_3437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType___boxed(lean_object* v_env_3438_, lean_object* v_ty_3439_){
_start:
{
uint8_t v_res_3440_; lean_object* v_r_3441_; 
v_res_3440_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v_env_3438_, v_ty_3439_);
lean_dec_ref(v_ty_3439_);
v_r_3441_ = lean_box(v_res_3440_);
return v_r_3441_;
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
res = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_();
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
res = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Do_SpecAttr_specAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_specAttr);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
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
