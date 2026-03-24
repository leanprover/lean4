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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1;
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "Invalid 'spec': target was neither a Hoare triple specification nor a 'simp' lemma"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Reason for failure to apply spec attribute: "};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "mvcgen_invariant_type"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 10, 73, 86, 132, 163, 253, 140)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "marks a type as an invariant type for the `mvcgen` tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "mvcgenInvariantAttr"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 109, 122, 82, 215, 148, 2, 116)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 244, 136, 137, 73, 53, 158, 220)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenInvariantAttr;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isMVCGenInvariantType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_isMVCGenInvariantType___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "mvcgen_witness_type"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 112, 69, 130, 225, 254, 106, 231)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "marks a type as a witness type for the `mvcgen` tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "mvcgenWitnessTypeAttr"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 109, 122, 82, 215, 148, 2, 116)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 191, 137, 104, 47, 203, 137, 70)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenWitnessTypeAttr;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isMVCGenWitnessType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_isMVCGenWitnessType___boxed(lean_object*, lean_object*);
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
lean_inc(v_declName_535_);
lean_dec_ref(v_x_529_);
lean_inc(v_declName_535_);
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
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0));
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
return v___x_1140_;
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
v___x_1235_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1);
lean_inc(v_k_1234_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_k_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
lean_inc(v_k_1234_);
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
v___x_1350_ = lean_panic_fn(v___x_1349_, v_msg_1348_);
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
lean_object* v___x_1988_; lean_object* v_config_1989_; uint8_t v_foApprox_1990_; uint8_t v_ctxApprox_1991_; uint8_t v_quasiPatternApprox_1992_; uint8_t v_constApprox_1993_; uint8_t v_isDefEqStuckEx_1994_; uint8_t v_unificationHints_1995_; uint8_t v_proofIrrelevance_1996_; uint8_t v_assignSyntheticOpaque_1997_; uint8_t v_offsetCnstrs_1998_; uint8_t v_transparency_1999_; uint8_t v_etaStruct_2000_; uint8_t v_univApprox_2001_; uint8_t v_zetaUnused_2002_; uint8_t v_zetaHave_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2013_; 
v___x_1988_ = l_Lean_Meta_simpGlobalConfig;
v_config_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref(v_config_1989_);
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
v_isSharedCheck_2013_ = !lean_is_exclusive(v_config_1989_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2005_ = v_config_1989_;
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
else
{
lean_dec(v_config_1989_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
uint8_t v___x_2007_; uint8_t v___x_2008_; lean_object* v___x_2010_; 
v___x_2007_ = 1;
v___x_2008_ = 2;
if (v_isShared_2006_ == 0)
{
v___x_2010_ = v___x_2005_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 0, v_foApprox_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 1, v_ctxApprox_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 2, v_quasiPatternApprox_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 3, v_constApprox_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 4, v_isDefEqStuckEx_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 5, v_unificationHints_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 6, v_proofIrrelevance_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 7, v_assignSyntheticOpaque_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 8, v_offsetCnstrs_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 9, v_transparency_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 10, v_etaStruct_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 11, v_univApprox_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 17, v_zetaUnused_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, 18, v_zetaHave_2003_);
v___x_2010_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; 
lean_ctor_set_uint8(v___x_2010_, 12, v___x_2007_);
lean_ctor_set_uint8(v___x_2010_, 13, v___x_2007_);
lean_ctor_set_uint8(v___x_2010_, 14, v___x_2008_);
lean_ctor_set_uint8(v___x_2010_, 15, v___x_2007_);
lean_ctor_set_uint8(v___x_2010_, 16, v___x_2007_);
v___x_2011_ = l_Lean_Meta_Config_toConfigWithKey(v___x_2010_);
return v___x_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(lean_object* v_k_2014_, uint8_t v_allowLevelAssignments_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2015_, v_k_2014_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_a_2030_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2021_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2021_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg___boxed(lean_object* v_k_2038_, lean_object* v_allowLevelAssignments_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2045_; lean_object* v_res_2046_; 
v_allowLevelAssignments_boxed_2045_ = lean_unbox(v_allowLevelAssignments_2039_);
v_res_2046_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_2038_, v_allowLevelAssignments_boxed_2045_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(lean_object* v_00_u03b1_2047_, lean_object* v_k_2048_, uint8_t v_allowLevelAssignments_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_2048_, v_allowLevelAssignments_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___boxed(lean_object* v_00_u03b1_2056_, lean_object* v_k_2057_, lean_object* v_allowLevelAssignments_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2064_; lean_object* v_res_2065_; 
v_allowLevelAssignments_boxed_2064_ = lean_unbox(v_allowLevelAssignments_2058_);
v_res_2065_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(v_00_u03b1_2056_, v_k_2057_, v_allowLevelAssignments_boxed_2064_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
return v_res_2065_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2073_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__4);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___x_2076_);
return v___x_2078_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_unsigned_to_nat(32u);
v___x_2080_ = lean_mk_empty_array_with_capacity(v___x_2079_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8(void){
_start:
{
size_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2082_ = ((size_t)5ULL);
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = lean_unsigned_to_nat(32u);
v___x_2085_ = lean_mk_empty_array_with_capacity(v___x_2084_);
v___x_2086_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__7);
v___x_2087_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___x_2085_);
lean_ctor_set(v___x_2087_, 2, v___x_2083_);
lean_ctor_set(v___x_2087_, 3, v___x_2083_);
lean_ctor_set_usize(v___x_2087_, 4, v___x_2082_);
return v___x_2087_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__8);
v___x_2089_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__5);
v___x_2090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
lean_ctor_set(v___x_2090_, 2, v___x_2089_);
lean_ctor_set(v___x_2090_, 3, v___x_2088_);
return v___x_2090_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__9);
v___x_2092_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__6);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v___x_2091_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(lean_object* v_a_2094_, lean_object* v_xs_2095_, lean_object* v_b_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_snd_2102_; lean_object* v_snd_2103_; lean_object* v_snd_2104_; lean_object* v_fst_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2232_; 
v_snd_2102_ = lean_ctor_get(v_b_2096_, 1);
lean_inc(v_snd_2102_);
v_snd_2103_ = lean_ctor_get(v_snd_2102_, 1);
lean_inc(v_snd_2103_);
v_snd_2104_ = lean_ctor_get(v_snd_2103_, 1);
lean_inc(v_snd_2104_);
v_fst_2105_ = lean_ctor_get(v_b_2096_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_b_2096_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; 
v_unused_2233_ = lean_ctor_get(v_b_2096_, 1);
lean_dec(v_unused_2233_);
v___x_2107_ = v_b_2096_;
v_isShared_2108_ = v_isSharedCheck_2232_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_fst_2105_);
lean_dec(v_b_2096_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2232_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v_fst_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2230_; 
v_fst_2109_ = lean_ctor_get(v_snd_2102_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_snd_2102_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v_snd_2102_, 1);
lean_dec(v_unused_2231_);
v___x_2111_ = v_snd_2102_;
v_isShared_2112_ = v_isSharedCheck_2230_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_fst_2109_);
lean_dec(v_snd_2102_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2230_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_fst_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2228_; 
v_fst_2113_ = lean_ctor_get(v_snd_2103_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_snd_2103_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v_snd_2103_, 1);
lean_dec(v_unused_2229_);
v___x_2115_ = v_snd_2103_;
v_isShared_2116_ = v_isSharedCheck_2228_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_fst_2113_);
lean_dec(v_snd_2103_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2228_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v_fst_2117_; lean_object* v_snd_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2227_; 
v_fst_2117_ = lean_ctor_get(v_snd_2104_, 0);
v_snd_2118_ = lean_ctor_get(v_snd_2104_, 1);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_snd_2104_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2120_ = v_snd_2104_;
v_isShared_2121_ = v_isSharedCheck_2227_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_snd_2118_);
lean_inc(v_fst_2117_);
lean_dec(v_snd_2104_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2227_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2122_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__2));
v___x_2123_ = lean_unsigned_to_nat(3u);
v___x_2124_ = l_Lean_Expr_isAppOfArity(v_fst_2105_, v___x_2122_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2126_; 
lean_dec_ref(v_a_2094_);
if (v_isShared_2121_ == 0)
{
v___x_2126_ = v___x_2120_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_fst_2117_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_snd_2118_);
v___x_2126_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 1, v___x_2126_);
v___x_2128_ = v___x_2115_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_fst_2113_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2128_);
v___x_2130_ = v___x_2111_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_fst_2109_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2132_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 1, v___x_2130_);
v___x_2132_ = v___x_2107_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_fst_2105_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
}
}
}
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_del_object(v___x_2107_);
v___x_2138_ = lean_unsigned_to_nat(1u);
v___x_2139_ = l_Lean_Expr_getAppNumArgs(v_fst_2105_);
v___x_2140_ = lean_nat_sub(v___x_2139_, v___x_2138_);
v___x_2141_ = lean_nat_sub(v___x_2140_, v___x_2138_);
lean_dec(v___x_2140_);
v___x_2142_ = l_Lean_Expr_getRevArg_x21(v_fst_2105_, v___x_2141_);
v___x_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
v___x_2144_ = 0;
v___x_2145_ = lean_box(0);
v___x_2146_ = l_Lean_Meta_mkFreshExprMVar(v___x_2143_, v___x_2144_, v___x_2145_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref(v___x_2146_);
v___x_2148_ = lean_mk_empty_array_with_capacity(v___x_2138_);
v___x_2149_ = lean_array_push(v___x_2148_, v_a_2147_);
v___x_2150_ = l_Lean_Expr_beta(v_fst_2109_, v___x_2149_);
v___x_2151_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__3));
v___x_2152_ = lean_box(0);
v___x_2153_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___closed__10);
lean_inc_ref(v_a_2094_);
v___x_2154_ = l_Lean_Meta_simp(v___x_2150_, v_a_2094_, v___x_2151_, v___x_2152_, v___x_2153_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v_fst_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2209_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v_fst_2156_ = lean_ctor_get(v_a_2155_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_a_2155_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v_a_2155_, 1);
lean_dec(v_unused_2210_);
v___x_2158_ = v_a_2155_;
v_isShared_2159_ = v_isSharedCheck_2209_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_fst_2156_);
lean_dec(v_a_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2209_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v_expr_2160_; lean_object* v___x_2161_; 
v_expr_2160_ = lean_ctor_get(v_fst_2156_, 0);
lean_inc_ref(v_expr_2160_);
lean_dec(v_fst_2156_);
v___x_2161_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2095_, v_expr_2160_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2163_; lean_object* v_lastSuccess_2165_; lean_object* v_boundAssignments_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; uint8_t v___x_2198_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2161_);
v___x_2163_ = lean_nat_add(v_fst_2113_, v___x_2138_);
lean_dec(v_fst_2113_);
v___x_2198_ = lean_nat_dec_lt(v_a_2162_, v_snd_2118_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2199_ = l_Lean_Expr_getAppFn_x27(v_expr_2160_);
v___x_2200_ = l_Lean_Expr_isMVar(v___x_2199_);
lean_dec_ref(v___x_2199_);
if (v___x_2200_ == 0)
{
lean_dec(v_a_2162_);
v_lastSuccess_2165_ = v_fst_2117_;
v_boundAssignments_2166_ = v_snd_2118_;
v___y_2167_ = v___y_2097_;
v___y_2168_ = v___y_2098_;
v___y_2169_ = v___y_2099_;
v___y_2170_ = v___y_2100_;
goto v___jp_2164_;
}
else
{
lean_dec(v_snd_2118_);
lean_dec(v_fst_2117_);
lean_inc(v___x_2163_);
v_lastSuccess_2165_ = v___x_2163_;
v_boundAssignments_2166_ = v_a_2162_;
v___y_2167_ = v___y_2097_;
v___y_2168_ = v___y_2098_;
v___y_2169_ = v___y_2099_;
v___y_2170_ = v___y_2100_;
goto v___jp_2164_;
}
}
else
{
lean_dec(v_snd_2118_);
lean_dec(v_fst_2117_);
lean_inc(v___x_2163_);
v_lastSuccess_2165_ = v___x_2163_;
v_boundAssignments_2166_ = v_a_2162_;
v___y_2167_ = v___y_2097_;
v___y_2168_ = v___y_2098_;
v___y_2169_ = v___y_2099_;
v___y_2170_ = v___y_2100_;
goto v___jp_2164_;
}
v___jp_2164_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2171_ = lean_unsigned_to_nat(2u);
v___x_2172_ = lean_nat_sub(v___x_2139_, v___x_2171_);
lean_dec(v___x_2139_);
v___x_2173_ = lean_nat_sub(v___x_2172_, v___x_2138_);
lean_dec(v___x_2172_);
v___x_2174_ = l_Lean_Expr_getRevArg_x21(v_fst_2105_, v___x_2173_);
lean_dec(v_fst_2105_);
v___x_2175_ = l_Lean_Meta_whnfR(v___x_2174_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref(v___x_2175_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 1, v_boundAssignments_2166_);
lean_ctor_set(v___x_2158_, 0, v_lastSuccess_2165_);
v___x_2178_ = v___x_2158_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_lastSuccess_2165_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_boundAssignments_2166_);
v___x_2178_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v___x_2178_);
lean_ctor_set(v___x_2120_, 0, v___x_2163_);
v___x_2180_ = v___x_2120_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2182_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 1, v___x_2180_);
lean_ctor_set(v___x_2115_, 0, v_expr_2160_);
v___x_2182_ = v___x_2115_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_expr_2160_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2182_);
lean_ctor_set(v___x_2111_, 0, v_a_2176_);
v___x_2184_ = v___x_2111_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2176_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
v_b_2096_ = v___x_2184_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_boundAssignments_2166_);
lean_dec(v_lastSuccess_2165_);
lean_dec(v___x_2163_);
lean_dec_ref(v_expr_2160_);
lean_del_object(v___x_2158_);
lean_del_object(v___x_2120_);
lean_del_object(v___x_2115_);
lean_del_object(v___x_2111_);
lean_dec_ref(v_a_2094_);
v_a_2190_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2175_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2175_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref(v_expr_2160_);
lean_del_object(v___x_2158_);
lean_dec(v___x_2139_);
lean_del_object(v___x_2120_);
lean_dec(v_snd_2118_);
lean_dec(v_fst_2117_);
lean_del_object(v___x_2115_);
lean_dec(v_fst_2113_);
lean_del_object(v___x_2111_);
lean_dec(v_fst_2105_);
lean_dec_ref(v_a_2094_);
v_a_2201_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2161_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2161_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v___x_2139_);
lean_del_object(v___x_2120_);
lean_dec(v_snd_2118_);
lean_dec(v_fst_2117_);
lean_del_object(v___x_2115_);
lean_dec(v_fst_2113_);
lean_del_object(v___x_2111_);
lean_dec(v_fst_2105_);
lean_dec_ref(v_a_2094_);
v_a_2211_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2154_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2154_);
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
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v___x_2139_);
lean_del_object(v___x_2120_);
lean_dec(v_snd_2118_);
lean_dec(v_fst_2117_);
lean_del_object(v___x_2115_);
lean_dec(v_fst_2113_);
lean_del_object(v___x_2111_);
lean_dec(v_fst_2109_);
lean_dec(v_fst_2105_);
lean_dec_ref(v_a_2094_);
v_a_2219_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2146_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2146_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___boxed(lean_object* v_a_2234_, lean_object* v_xs_2235_, lean_object* v_b_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(v_a_2234_, v_xs_2235_, v_b_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_xs_2235_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(lean_object* v___x_2243_, uint8_t v___x_2244_, lean_object* v_00_u03c3s_2245_, lean_object* v_xs_2246_, lean_object* v_e_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
if (v___x_2244_ == 0)
{
lean_object* v_config_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2327_; 
v_config_2253_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2255_ = v___x_2243_;
v_isShared_2256_ = v_isSharedCheck_2327_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_config_2253_);
lean_dec(v___x_2243_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2327_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
uint8_t v_trackZetaDelta_2257_; lean_object* v_zetaDeltaSet_2258_; lean_object* v_lctx_2259_; lean_object* v_localInstances_2260_; lean_object* v_defEqCtx_x3f_2261_; lean_object* v_synthPendingDepth_2262_; lean_object* v_canUnfold_x3f_2263_; uint8_t v_univApprox_2264_; uint8_t v_inTypeClassResolution_2265_; uint8_t v_cacheInferType_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2325_; 
v_trackZetaDelta_2257_ = lean_ctor_get_uint8(v___y_2248_, sizeof(void*)*7);
v_zetaDeltaSet_2258_ = lean_ctor_get(v___y_2248_, 1);
v_lctx_2259_ = lean_ctor_get(v___y_2248_, 2);
v_localInstances_2260_ = lean_ctor_get(v___y_2248_, 3);
v_defEqCtx_x3f_2261_ = lean_ctor_get(v___y_2248_, 4);
v_synthPendingDepth_2262_ = lean_ctor_get(v___y_2248_, 5);
v_canUnfold_x3f_2263_ = lean_ctor_get(v___y_2248_, 6);
v_univApprox_2264_ = lean_ctor_get_uint8(v___y_2248_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2265_ = lean_ctor_get_uint8(v___y_2248_, sizeof(void*)*7 + 2);
v_cacheInferType_2266_ = lean_ctor_get_uint8(v___y_2248_, sizeof(void*)*7 + 3);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___y_2248_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v___y_2248_, 0);
lean_dec(v_unused_2326_);
v___x_2268_ = v___y_2248_;
v_isShared_2269_ = v_isSharedCheck_2325_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_canUnfold_x3f_2263_);
lean_inc(v_synthPendingDepth_2262_);
lean_inc(v_defEqCtx_x3f_2261_);
lean_inc(v_localInstances_2260_);
lean_inc(v_lctx_2259_);
lean_inc(v_zetaDeltaSet_2258_);
lean_dec(v___y_2248_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2325_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
uint64_t v___x_2270_; lean_object* v___x_2272_; 
v___x_2270_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2253_);
if (v_isShared_2256_ == 0)
{
v___x_2272_ = v___x_2255_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_config_2253_);
v___x_2272_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2274_; 
lean_ctor_set_uint64(v___x_2272_, sizeof(void*)*1, v___x_2270_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2272_);
v___x_2274_ = v___x_2268_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_zetaDeltaSet_2258_);
lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_lctx_2259_);
lean_ctor_set(v_reuseFailAlloc_2323_, 3, v_localInstances_2260_);
lean_ctor_set(v_reuseFailAlloc_2323_, 4, v_defEqCtx_x3f_2261_);
lean_ctor_set(v_reuseFailAlloc_2323_, 5, v_synthPendingDepth_2262_);
lean_ctor_set(v_reuseFailAlloc_2323_, 6, v_canUnfold_x3f_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2323_, sizeof(void*)*7, v_trackZetaDelta_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2323_, sizeof(void*)*7 + 1, v_univApprox_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2323_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2323_, sizeof(void*)*7 + 3, v_cacheInferType_2266_);
v___x_2274_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v___x_2274_, v___y_2250_, v___y_2251_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2277_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
v___x_2277_ = l_Lean_Meta_whnfR(v_00_u03c3s_2245_, v___x_2274_, v___y_2249_, v___y_2250_, v___y_2251_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref(v___x_2277_);
v___x_2279_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2246_, v_e_2247_, v___x_2274_, v___y_2249_, v___y_2250_, v___y_2251_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
v___x_2281_ = lean_unsigned_to_nat(0u);
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v_a_2280_);
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2281_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v_e_2247_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v_a_2278_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(v_a_2276_, v_xs_2246_, v___x_2285_, v___x_2274_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec_ref(v___x_2274_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2298_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2298_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2298_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v_snd_2291_; lean_object* v_snd_2292_; lean_object* v_snd_2293_; lean_object* v_fst_2294_; lean_object* v___x_2296_; 
v_snd_2291_ = lean_ctor_get(v_a_2287_, 1);
lean_inc(v_snd_2291_);
lean_dec(v_a_2287_);
v_snd_2292_ = lean_ctor_get(v_snd_2291_, 1);
lean_inc(v_snd_2292_);
lean_dec(v_snd_2291_);
v_snd_2293_ = lean_ctor_get(v_snd_2292_, 1);
lean_inc(v_snd_2293_);
lean_dec(v_snd_2292_);
v_fst_2294_ = lean_ctor_get(v_snd_2293_, 0);
lean_inc(v_fst_2294_);
lean_dec(v_snd_2293_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v_fst_2294_);
v___x_2296_ = v___x_2289_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_fst_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v_a_2299_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2286_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2286_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_dec(v_a_2278_);
lean_dec(v_a_2276_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v_e_2247_);
return v___x_2279_;
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_a_2276_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v_e_2247_);
v_a_2307_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2277_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2277_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v___x_2274_);
lean_dec_ref(v_e_2247_);
lean_dec_ref(v_00_u03c3s_2245_);
v_a_2315_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2275_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2275_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
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
lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec_ref(v___y_2248_);
lean_dec_ref(v_e_2247_);
lean_dec_ref(v_00_u03c3s_2245_);
lean_dec_ref(v___x_2243_);
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed(lean_object* v___x_2330_, lean_object* v___x_2331_, lean_object* v_00_u03c3s_2332_, lean_object* v_xs_2333_, lean_object* v_e_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
uint8_t v___x_4177__boxed_2340_; lean_object* v_res_2341_; 
v___x_4177__boxed_2340_ = lean_unbox(v___x_2331_);
v_res_2341_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(v___x_2330_, v___x_4177__boxed_2340_, v_00_u03c3s_2332_, v_xs_2333_, v_e_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v_xs_2333_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(lean_object* v_xs_2342_, lean_object* v_00_u03c3s_2343_, lean_object* v_e_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___f_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2350_ = l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig;
v___x_2351_ = lean_array_get_size(v_xs_2342_);
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = lean_nat_dec_eq(v___x_2351_, v___x_2352_);
v___x_2354_ = lean_box(v___x_2353_);
v___f_2355_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2355_, 0, v___x_2350_);
lean_closure_set(v___f_2355_, 1, v___x_2354_);
lean_closure_set(v___f_2355_, 2, v_00_u03c3s_2343_);
lean_closure_set(v___f_2355_, 3, v_xs_2342_);
lean_closure_set(v___f_2355_, 4, v_e_2344_);
v___x_2356_ = 0;
v___x_2357_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_2355_, v___x_2356_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___boxed(lean_object* v_xs_2358_, lean_object* v_00_u03c3s_2359_, lean_object* v_e_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_xs_2358_, v_00_u03c3s_2359_, v_e_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2366_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0));
v___x_2369_ = l_Lean_stringToMessageData(v___x_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(lean_object* v_a_2383_, lean_object* v___x_2384_, uint8_t v___x_2385_, lean_object* v___x_2386_, lean_object* v_proof_2387_, lean_object* v_prio_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v_config_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2527_; 
v___x_2394_ = l_Lean_Meta_simpGlobalConfig;
v_config_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2527_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_config_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2527_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
uint8_t v_trackZetaDelta_2399_; lean_object* v_zetaDeltaSet_2400_; lean_object* v_lctx_2401_; lean_object* v_localInstances_2402_; lean_object* v_defEqCtx_x3f_2403_; lean_object* v_synthPendingDepth_2404_; lean_object* v_canUnfold_x3f_2405_; uint8_t v_univApprox_2406_; uint8_t v_inTypeClassResolution_2407_; uint8_t v_cacheInferType_2408_; uint64_t v___x_2409_; lean_object* v___x_2411_; 
v_trackZetaDelta_2399_ = lean_ctor_get_uint8(v___y_2389_, sizeof(void*)*7);
v_zetaDeltaSet_2400_ = lean_ctor_get(v___y_2389_, 1);
v_lctx_2401_ = lean_ctor_get(v___y_2389_, 2);
v_localInstances_2402_ = lean_ctor_get(v___y_2389_, 3);
v_defEqCtx_x3f_2403_ = lean_ctor_get(v___y_2389_, 4);
v_synthPendingDepth_2404_ = lean_ctor_get(v___y_2389_, 5);
v_canUnfold_x3f_2405_ = lean_ctor_get(v___y_2389_, 6);
v_univApprox_2406_ = lean_ctor_get_uint8(v___y_2389_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2407_ = lean_ctor_get_uint8(v___y_2389_, sizeof(void*)*7 + 2);
v_cacheInferType_2408_ = lean_ctor_get_uint8(v___y_2389_, sizeof(void*)*7 + 3);
v___x_2409_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2395_);
if (v_isShared_2398_ == 0)
{
v___x_2411_ = v___x_2397_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_config_2395_);
v___x_2411_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_ctor_set_uint64(v___x_2411_, sizeof(void*)*1, v___x_2409_);
lean_inc(v_canUnfold_x3f_2405_);
lean_inc(v_synthPendingDepth_2404_);
lean_inc(v_defEqCtx_x3f_2403_);
lean_inc_ref(v_localInstances_2402_);
lean_inc_ref(v_lctx_2401_);
lean_inc(v_zetaDeltaSet_2400_);
v___x_2412_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
lean_ctor_set(v___x_2412_, 1, v_zetaDeltaSet_2400_);
lean_ctor_set(v___x_2412_, 2, v_lctx_2401_);
lean_ctor_set(v___x_2412_, 3, v_localInstances_2402_);
lean_ctor_set(v___x_2412_, 4, v_defEqCtx_x3f_2403_);
lean_ctor_set(v___x_2412_, 5, v_synthPendingDepth_2404_);
lean_ctor_set(v___x_2412_, 6, v_canUnfold_x3f_2405_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*7, v_trackZetaDelta_2399_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*7 + 1, v_univApprox_2406_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2407_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*7 + 3, v_cacheInferType_2408_);
v___x_2413_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2383_, v___x_2384_, v___x_2385_, v___x_2412_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec_ref(v___x_2412_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v_snd_2415_; lean_object* v_fst_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2517_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref(v___x_2413_);
v_snd_2415_ = lean_ctor_get(v_a_2414_, 1);
v_fst_2416_ = lean_ctor_get(v_a_2414_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_a_2414_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2418_ = v_a_2414_;
v_isShared_2419_ = v_isSharedCheck_2517_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_snd_2415_);
lean_inc(v_fst_2416_);
lean_dec(v_a_2414_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2517_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_snd_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2515_; 
v_snd_2420_ = lean_ctor_get(v_snd_2415_, 1);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_snd_2415_);
if (v_isSharedCheck_2515_ == 0)
{
lean_object* v_unused_2516_; 
v_unused_2516_ = lean_ctor_get(v_snd_2415_, 0);
lean_dec(v_unused_2516_);
v___x_2422_ = v_snd_2415_;
v_isShared_2423_ = v_isSharedCheck_2515_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_snd_2420_);
lean_dec(v_snd_2415_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2515_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_Meta_whnfR(v_snd_2420_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref(v___x_2424_);
lean_inc(v_a_2425_);
v___x_2437_ = l_Lean_Expr_cleanupAnnotations(v_a_2425_);
v___x_2438_ = l_Lean_Expr_isApp(v___x_2437_);
if (v___x_2438_ == 0)
{
lean_dec_ref(v___x_2437_);
lean_del_object(v___x_2418_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v___y_2427_ = v___y_2389_;
v___y_2428_ = v___y_2390_;
v___y_2429_ = v___y_2391_;
v___y_2430_ = v___y_2392_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2437_);
v___x_2440_ = l_Lean_Expr_isApp(v___x_2439_);
if (v___x_2440_ == 0)
{
lean_dec_ref(v___x_2439_);
lean_del_object(v___x_2418_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v___y_2427_ = v___y_2389_;
v___y_2428_ = v___y_2390_;
v___y_2429_ = v___y_2391_;
v___y_2430_ = v___y_2392_;
goto v___jp_2426_;
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
lean_del_object(v___x_2418_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v___y_2427_ = v___y_2389_;
v___y_2428_ = v___y_2390_;
v___y_2429_ = v___y_2391_;
v___y_2430_ = v___y_2392_;
goto v___jp_2426_;
}
else
{
lean_object* v_arg_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v_arg_2444_ = lean_ctor_get(v___x_2442_, 1);
lean_inc_ref(v_arg_2444_);
v___x_2445_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2442_);
v___x_2446_ = l_Lean_Expr_isApp(v___x_2445_);
if (v___x_2446_ == 0)
{
lean_dec_ref(v___x_2445_);
lean_dec_ref(v_arg_2444_);
lean_dec_ref(v_arg_2441_);
lean_del_object(v___x_2418_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v___y_2427_ = v___y_2389_;
v___y_2428_ = v___y_2390_;
v___y_2429_ = v___y_2391_;
v___y_2430_ = v___y_2392_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2445_);
v___x_2448_ = l_Lean_Expr_isApp(v___x_2447_);
if (v___x_2448_ == 0)
{
lean_dec_ref(v___x_2447_);
lean_dec_ref(v_arg_2444_);
lean_dec_ref(v_arg_2441_);
lean_del_object(v___x_2418_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v___y_2427_ = v___y_2389_;
v___y_2428_ = v___y_2390_;
v___y_2429_ = v___y_2391_;
v___y_2430_ = v___y_2392_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2447_);
v___x_2450_ = l_Lean_Expr_isApp(v___x_2449_);
if (v___x_2450_ == 0)
{
lean_dec_ref(v___x_2449_);
lean_dec_ref(v_arg_2444_);
lean_dec_ref(v_arg_2441_);
lean_del_object(v___x_2418_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v___y_2427_ = v___y_2389_;
v___y_2428_ = v___y_2390_;
v___y_2429_ = v___y_2391_;
v___y_2430_ = v___y_2392_;
goto v___jp_2426_;
}
else
{
lean_object* v_arg_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v_arg_2451_ = lean_ctor_get(v___x_2449_, 1);
lean_inc_ref(v_arg_2451_);
v___x_2452_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2449_);
v___x_2453_ = l_Lean_Expr_isApp(v___x_2452_);
if (v___x_2453_ == 0)
{
lean_dec_ref(v___x_2452_);
lean_dec_ref(v_arg_2451_);
lean_dec_ref(v_arg_2444_);
lean_dec_ref(v_arg_2441_);
lean_del_object(v___x_2418_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v___y_2427_ = v___y_2389_;
v___y_2428_ = v___y_2390_;
v___y_2429_ = v___y_2391_;
v___y_2430_ = v___y_2392_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2454_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2452_);
v___x_2455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4));
v___x_2456_ = l_Lean_Expr_isConstOf(v___x_2454_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_dec_ref(v___x_2454_);
lean_dec_ref(v_arg_2451_);
lean_dec_ref(v_arg_2444_);
lean_dec_ref(v_arg_2441_);
lean_del_object(v___x_2418_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v___y_2427_ = v___y_2389_;
v___y_2428_ = v___y_2390_;
v___y_2429_ = v___y_2391_;
v___y_2430_ = v___y_2392_;
goto v___jp_2426_;
}
else
{
uint8_t v___x_2457_; lean_object* v___x_2458_; 
lean_dec(v_a_2425_);
lean_del_object(v___x_2422_);
v___x_2457_ = 0;
lean_inc_ref(v_arg_2444_);
v___x_2458_ = l_Lean_Meta_DiscrTree_mkPath(v_arg_2444_, v___x_2457_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref(v___x_2458_);
v___x_2460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7));
v___x_2461_ = l_Lean_Expr_constLevels_x21(v___x_2454_);
lean_dec_ref(v___x_2454_);
v___x_2462_ = lean_unsigned_to_nat(0u);
v___x_2463_ = l_List_get_x21Internal___redArg(v___x_2386_, v___x_2461_, v___x_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
if (v_isShared_2419_ == 0)
{
lean_ctor_set_tag(v___x_2418_, 1);
lean_ctor_set(v___x_2418_, 1, v___x_2464_);
lean_ctor_set(v___x_2418_, 0, v___x_2463_);
v___x_2466_ = v___x_2418_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = l_Lean_mkConst(v___x_2460_, v___x_2466_);
v___x_2468_ = l_Lean_Expr_app___override(v___x_2467_, v_arg_2451_);
lean_inc(v_fst_2416_);
v___x_2469_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_fst_2416_, v___x_2468_, v_arg_2441_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref(v___x_2469_);
v___x_2471_ = 1;
v___x_2472_ = l_Lean_Meta_mkForallFVars(v_fst_2416_, v_arg_2444_, v___x_2457_, v___x_2456_, v___x_2456_, v___x_2471_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v_fst_2416_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2481_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2481_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2481_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2477_, 0, v_a_2459_);
lean_ctor_set(v___x_2477_, 1, v_a_2473_);
lean_ctor_set(v___x_2477_, 2, v_proof_2387_);
lean_ctor_set(v___x_2477_, 3, v_a_2470_);
lean_ctor_set(v___x_2477_, 4, v_prio_2388_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2477_);
v___x_2479_ = v___x_2475_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_a_2470_);
lean_dec(v_a_2459_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
v_a_2482_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2472_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2472_);
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
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v_a_2459_);
lean_dec_ref(v_arg_2444_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
v_a_2490_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2469_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2469_);
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
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec_ref(v___x_2454_);
lean_dec_ref(v_arg_2451_);
lean_dec_ref(v_arg_2444_);
lean_dec_ref(v_arg_2441_);
lean_del_object(v___x_2418_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v_a_2499_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2458_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2458_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
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
v___jp_2426_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2431_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1);
v___x_2432_ = l_Lean_indentExpr(v_a_2425_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 7);
lean_ctor_set(v___x_2422_, 1, v___x_2432_);
lean_ctor_set(v___x_2422_, 0, v___x_2431_);
v___x_2434_ = v___x_2422_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2434_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
return v___x_2435_;
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_del_object(v___x_2422_);
lean_del_object(v___x_2418_);
lean_dec(v_fst_2416_);
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v_a_2507_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2424_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2424_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v_prio_2388_);
lean_dec_ref(v_proof_2387_);
lean_dec(v___x_2386_);
v_a_2518_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2413_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2413_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed(lean_object* v_a_2528_, lean_object* v___x_2529_, lean_object* v___x_2530_, lean_object* v___x_2531_, lean_object* v_proof_2532_, lean_object* v_prio_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
uint8_t v___x_3663__boxed_2539_; lean_object* v_res_2540_; 
v___x_3663__boxed_2539_ = lean_unbox(v___x_2530_);
v_res_2540_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(v_a_2528_, v___x_2529_, v___x_3663__boxed_2539_, v___x_2531_, v_proof_2532_, v_prio_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2540_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0));
v___x_2543_ = l_Lean_stringToMessageData(v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(lean_object* v_type_2544_, lean_object* v_proof_2545_, lean_object* v_prio_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v___x_2552_; lean_object* v_a_2553_; lean_object* v___x_2554_; 
v___x_2552_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_type_2544_, v_a_2548_);
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2552_);
lean_inc(v_a_2553_);
v___x_2554_ = l_Lean_Meta_isProp(v_a_2553_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2556_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; uint8_t v___x_2568_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref(v___x_2554_);
v___x_2556_ = lean_box(0);
v___x_2568_ = lean_unbox(v_a_2555_);
lean_dec(v_a_2555_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_prio_2546_);
lean_dec_ref(v_proof_2545_);
v___x_2569_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1);
v___x_2570_ = l_Lean_indentExpr(v_a_2553_);
v___x_2571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2571_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
else
{
v___y_2558_ = v_a_2547_;
v___y_2559_ = v_a_2548_;
v___y_2560_ = v_a_2549_;
v___y_2561_ = v_a_2550_;
goto v___jp_2557_;
}
v___jp_2557_:
{
lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___f_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; 
v___x_2562_ = lean_box(0);
v___x_2563_ = 0;
v___x_2564_ = lean_box(v___x_2563_);
v___f_2565_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2565_, 0, v_a_2553_);
lean_closure_set(v___f_2565_, 1, v___x_2562_);
lean_closure_set(v___f_2565_, 2, v___x_2564_);
lean_closure_set(v___f_2565_, 3, v___x_2556_);
lean_closure_set(v___f_2565_, 4, v_proof_2545_);
lean_closure_set(v___f_2565_, 5, v_prio_2546_);
v___x_2566_ = 0;
v___x_2567_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_2565_, v___x_2566_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
return v___x_2567_;
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_a_2553_);
lean_dec(v_prio_2546_);
lean_dec_ref(v_proof_2545_);
v_a_2581_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2554_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2554_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___boxed(lean_object* v_type_2589_, lean_object* v_proof_2590_, lean_object* v_prio_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_type_2589_, v_proof_2590_, v_prio_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(lean_object* v_declName_2598_, lean_object* v_prio_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v___x_2605_; 
lean_inc(v_declName_2598_);
v___x_2605_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_2598_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref(v___x_2605_);
v___x_2607_ = l_Lean_ConstantInfo_levelParams(v_a_2606_);
lean_dec(v_a_2606_);
v___x_2608_ = lean_box(0);
v___x_2609_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_2607_, v___x_2608_);
lean_inc(v_declName_2598_);
v___x_2610_ = l_Lean_mkConst(v_declName_2598_, v___x_2609_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2611_ = lean_infer_type(v___x_2610_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref(v___x_2611_);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v_declName_2598_);
v___x_2614_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_2612_, v___x_2613_, v_prio_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
return v___x_2614_;
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec(v_prio_2599_);
lean_dec(v_declName_2598_);
v_a_2615_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2611_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2611_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_prio_2599_);
lean_dec(v_declName_2598_);
v_a_2623_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2605_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2605_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst___boxed(lean_object* v_declName_2631_, lean_object* v_prio_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_2631_, v_prio_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
return v_res_2638_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0));
v___x_2641_ = l_Lean_stringToMessageData(v___x_2640_);
return v___x_2641_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2));
v___x_2644_ = l_Lean_stringToMessageData(v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(lean_object* v_fvar_2645_, lean_object* v_prio_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v___x_2652_; 
lean_inc_ref(v_a_2647_);
lean_inc(v_fvar_2645_);
v___x_2652_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvar_2645_, v_a_2647_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
if (lean_obj_tag(v_a_2653_) == 1)
{
lean_object* v_val_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2663_; 
v_val_2654_ = lean_ctor_get(v_a_2653_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_a_2653_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2656_ = v_a_2653_;
v_isShared_2657_ = v_isSharedCheck_2663_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_val_2654_);
lean_dec(v_a_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2663_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = l_Lean_LocalDecl_type(v_val_2654_);
lean_dec(v_val_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v_fvar_2645_);
v___x_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_fvar_2645_);
v___x_2660_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
lean_object* v___x_2661_; 
v___x_2661_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v___x_2658_, v___x_2660_, v_prio_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
return v___x_2661_;
}
}
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec(v_a_2653_);
lean_dec(v_prio_2646_);
v___x_2664_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1);
v___x_2665_ = l_Lean_MessageData_ofName(v_fvar_2645_);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2668_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
return v___x_2669_;
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v_prio_2646_);
lean_dec(v_fvar_2645_);
v_a_2670_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2652_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2652_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___boxed(lean_object* v_fvar_2678_, lean_object* v_prio_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvar_2678_, v_prio_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(lean_object* v___y_2686_){
_start:
{
lean_object* v___x_2688_; lean_object* v_ngen_2689_; lean_object* v_namePrefix_2690_; lean_object* v_idx_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2720_; 
v___x_2688_ = lean_st_ref_get(v___y_2686_);
v_ngen_2689_ = lean_ctor_get(v___x_2688_, 2);
lean_inc_ref(v_ngen_2689_);
lean_dec(v___x_2688_);
v_namePrefix_2690_ = lean_ctor_get(v_ngen_2689_, 0);
v_idx_2691_ = lean_ctor_get(v_ngen_2689_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_ngen_2689_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2693_ = v_ngen_2689_;
v_isShared_2694_ = v_isSharedCheck_2720_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_idx_2691_);
lean_inc(v_namePrefix_2690_);
lean_dec(v_ngen_2689_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2720_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v_env_2696_; lean_object* v_nextMacroScope_2697_; lean_object* v_auxDeclNGen_2698_; lean_object* v_traceState_2699_; lean_object* v_cache_2700_; lean_object* v_messages_2701_; lean_object* v_infoState_2702_; lean_object* v_snapshotTasks_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2718_; 
v___x_2695_ = lean_st_ref_take(v___y_2686_);
v_env_2696_ = lean_ctor_get(v___x_2695_, 0);
v_nextMacroScope_2697_ = lean_ctor_get(v___x_2695_, 1);
v_auxDeclNGen_2698_ = lean_ctor_get(v___x_2695_, 3);
v_traceState_2699_ = lean_ctor_get(v___x_2695_, 4);
v_cache_2700_ = lean_ctor_get(v___x_2695_, 5);
v_messages_2701_ = lean_ctor_get(v___x_2695_, 6);
v_infoState_2702_ = lean_ctor_get(v___x_2695_, 7);
v_snapshotTasks_2703_ = lean_ctor_get(v___x_2695_, 8);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v___x_2695_, 2);
lean_dec(v_unused_2719_);
v___x_2705_ = v___x_2695_;
v_isShared_2706_ = v_isSharedCheck_2718_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_snapshotTasks_2703_);
lean_inc(v_infoState_2702_);
lean_inc(v_messages_2701_);
lean_inc(v_cache_2700_);
lean_inc(v_traceState_2699_);
lean_inc(v_auxDeclNGen_2698_);
lean_inc(v_nextMacroScope_2697_);
lean_inc(v_env_2696_);
lean_dec(v___x_2695_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2718_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v_r_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2711_; 
lean_inc(v_idx_2691_);
lean_inc(v_namePrefix_2690_);
v_r_2707_ = l_Lean_Name_num___override(v_namePrefix_2690_, v_idx_2691_);
v___x_2708_ = lean_unsigned_to_nat(1u);
v___x_2709_ = lean_nat_add(v_idx_2691_, v___x_2708_);
lean_dec(v_idx_2691_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v___x_2709_);
v___x_2711_ = v___x_2693_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_namePrefix_2690_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
lean_object* v___x_2713_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 2, v___x_2711_);
v___x_2713_ = v___x_2705_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_env_2696_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v_nextMacroScope_2697_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v___x_2711_);
lean_ctor_set(v_reuseFailAlloc_2716_, 3, v_auxDeclNGen_2698_);
lean_ctor_set(v_reuseFailAlloc_2716_, 4, v_traceState_2699_);
lean_ctor_set(v_reuseFailAlloc_2716_, 5, v_cache_2700_);
lean_ctor_set(v_reuseFailAlloc_2716_, 6, v_messages_2701_);
lean_ctor_set(v_reuseFailAlloc_2716_, 7, v_infoState_2702_);
lean_ctor_set(v_reuseFailAlloc_2716_, 8, v_snapshotTasks_2703_);
v___x_2713_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = lean_st_ref_set(v___y_2686_, v___x_2713_);
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v_r_2707_);
return v___x_2715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg___boxed(lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_2721_);
lean_dec(v___y_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___boxed(lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(lean_object* v_ref_2736_, lean_object* v_proof_2737_, lean_object* v_prio_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2744_; 
lean_inc(v_a_2742_);
lean_inc_ref(v_a_2741_);
lean_inc(v_a_2740_);
lean_inc_ref(v_a_2739_);
lean_inc_ref(v_proof_2737_);
v___x_2744_ = lean_infer_type(v_proof_2737_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v_a_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v___x_2744_);
v___x_2746_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v_a_2742_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
v___x_2748_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2748_, 0, v_a_2747_);
lean_ctor_set(v___x_2748_, 1, v_ref_2736_);
lean_ctor_set(v___x_2748_, 2, v_proof_2737_);
v___x_2749_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_2745_, v___x_2748_, v_prio_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
return v___x_2749_;
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_prio_2738_);
lean_dec_ref(v_proof_2737_);
lean_dec(v_ref_2736_);
v_a_2750_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2744_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2744_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx___boxed(lean_object* v_ref_2758_, lean_object* v_proof_2759_, lean_object* v_prio_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(v_ref_2758_, v_proof_2759_, v_prio_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
return v_res_2766_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2767_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0);
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
return v___x_2771_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
v___x_2773_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
lean_ctor_set(v___x_2773_, 2, v___x_2772_);
lean_ctor_set(v___x_2773_, 3, v___x_2772_);
lean_ctor_set(v___x_2773_, 4, v___x_2772_);
lean_ctor_set(v___x_2773_, 5, v___x_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(lean_object* v_ext_2774_, lean_object* v_b_2775_, uint8_t v_kind_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_currNamespace_2781_; lean_object* v___x_2782_; lean_object* v_env_2783_; lean_object* v_nextMacroScope_2784_; lean_object* v_ngen_2785_; lean_object* v_auxDeclNGen_2786_; lean_object* v_traceState_2787_; lean_object* v_messages_2788_; lean_object* v_infoState_2789_; lean_object* v_snapshotTasks_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2817_; 
v_currNamespace_2781_ = lean_ctor_get(v___y_2778_, 6);
lean_inc(v_currNamespace_2781_);
lean_dec_ref(v___y_2778_);
v___x_2782_ = lean_st_ref_take(v___y_2779_);
v_env_2783_ = lean_ctor_get(v___x_2782_, 0);
v_nextMacroScope_2784_ = lean_ctor_get(v___x_2782_, 1);
v_ngen_2785_ = lean_ctor_get(v___x_2782_, 2);
v_auxDeclNGen_2786_ = lean_ctor_get(v___x_2782_, 3);
v_traceState_2787_ = lean_ctor_get(v___x_2782_, 4);
v_messages_2788_ = lean_ctor_get(v___x_2782_, 6);
v_infoState_2789_ = lean_ctor_get(v___x_2782_, 7);
v_snapshotTasks_2790_ = lean_ctor_get(v___x_2782_, 8);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v___x_2782_, 5);
lean_dec(v_unused_2818_);
v___x_2792_ = v___x_2782_;
v_isShared_2793_ = v_isSharedCheck_2817_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_snapshotTasks_2790_);
lean_inc(v_infoState_2789_);
lean_inc(v_messages_2788_);
lean_inc(v_traceState_2787_);
lean_inc(v_auxDeclNGen_2786_);
lean_inc(v_ngen_2785_);
lean_inc(v_nextMacroScope_2784_);
lean_inc(v_env_2783_);
lean_dec(v___x_2782_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2817_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2794_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2783_, v_ext_2774_, v_b_2775_, v_kind_2776_, v_currNamespace_2781_);
v___x_2795_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 5, v___x_2795_);
lean_ctor_set(v___x_2792_, 0, v___x_2794_);
v___x_2797_ = v___x_2792_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_nextMacroScope_2784_);
lean_ctor_set(v_reuseFailAlloc_2816_, 2, v_ngen_2785_);
lean_ctor_set(v_reuseFailAlloc_2816_, 3, v_auxDeclNGen_2786_);
lean_ctor_set(v_reuseFailAlloc_2816_, 4, v_traceState_2787_);
lean_ctor_set(v_reuseFailAlloc_2816_, 5, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2816_, 6, v_messages_2788_);
lean_ctor_set(v_reuseFailAlloc_2816_, 7, v_infoState_2789_);
lean_ctor_set(v_reuseFailAlloc_2816_, 8, v_snapshotTasks_2790_);
v___x_2797_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v_mctx_2800_; lean_object* v_zetaDeltaFVarIds_2801_; lean_object* v_postponed_2802_; lean_object* v_diag_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2814_; 
v___x_2798_ = lean_st_ref_set(v___y_2779_, v___x_2797_);
v___x_2799_ = lean_st_ref_take(v___y_2777_);
v_mctx_2800_ = lean_ctor_get(v___x_2799_, 0);
v_zetaDeltaFVarIds_2801_ = lean_ctor_get(v___x_2799_, 2);
v_postponed_2802_ = lean_ctor_get(v___x_2799_, 3);
v_diag_2803_ = lean_ctor_get(v___x_2799_, 4);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2814_ == 0)
{
lean_object* v_unused_2815_; 
v_unused_2815_ = lean_ctor_get(v___x_2799_, 1);
lean_dec(v_unused_2815_);
v___x_2805_ = v___x_2799_;
v_isShared_2806_ = v_isSharedCheck_2814_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_diag_2803_);
lean_inc(v_postponed_2802_);
lean_inc(v_zetaDeltaFVarIds_2801_);
lean_inc(v_mctx_2800_);
lean_dec(v___x_2799_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2814_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2807_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 1, v___x_2807_);
v___x_2809_ = v___x_2805_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_mctx_2800_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_zetaDeltaFVarIds_2801_);
lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_postponed_2802_);
lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_diag_2803_);
v___x_2809_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = lean_st_ref_set(v___y_2777_, v___x_2809_);
v___x_2811_ = lean_box(0);
v___x_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
return v___x_2812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___boxed(lean_object* v_ext_2819_, lean_object* v_b_2820_, lean_object* v_kind_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
uint8_t v_kind_boxed_2826_; lean_object* v_res_2827_; 
v_kind_boxed_2826_ = lean_unbox(v_kind_2821_);
v_res_2827_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2819_, v_b_2820_, v_kind_boxed_2826_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec(v___y_2822_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(lean_object* v_00_u03b1_2828_, lean_object* v_00_u03b2_2829_, lean_object* v_00_u03c3_2830_, lean_object* v_ext_2831_, lean_object* v_b_2832_, uint8_t v_kind_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; 
lean_inc_ref(v___y_2836_);
v___x_2839_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2831_, v_b_2832_, v_kind_2833_, v___y_2835_, v___y_2836_, v___y_2837_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___boxed(lean_object* v_00_u03b1_2840_, lean_object* v_00_u03b2_2841_, lean_object* v_00_u03c3_2842_, lean_object* v_ext_2843_, lean_object* v_b_2844_, lean_object* v_kind_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
uint8_t v_kind_boxed_2851_; lean_object* v_res_2852_; 
v_kind_boxed_2851_ = lean_unbox(v_kind_2845_);
v_res_2852_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(v_00_u03b1_2840_, v_00_u03b2_2841_, v_00_u03c3_2842_, v_ext_2843_, v_b_2844_, v_kind_boxed_2851_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(lean_object* v_ext_2853_, lean_object* v_declName_2854_, lean_object* v_prio_2855_, uint8_t v_attrKind_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_2854_, v_prio_2855_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2864_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___x_2862_);
lean_inc_ref(v_a_2859_);
v___x_2864_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2853_, v_a_2863_, v_attrKind_2856_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2864_;
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec_ref(v_ext_2853_);
v_a_2865_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2862_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2862_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst___boxed(lean_object* v_ext_2873_, lean_object* v_declName_2874_, lean_object* v_prio_2875_, lean_object* v_attrKind_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
uint8_t v_attrKind_boxed_2882_; lean_object* v_res_2883_; 
v_attrKind_boxed_2882_ = lean_unbox(v_attrKind_2876_);
v_res_2883_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(v_ext_2873_, v_declName_2874_, v_prio_2875_, v_attrKind_boxed_2882_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(lean_object* v_ext_2884_, lean_object* v_fvar_2885_, lean_object* v_prio_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvar_2885_, v_prio_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; uint8_t v___x_2894_; lean_object* v___x_2895_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref(v___x_2892_);
v___x_2894_ = 1;
lean_inc_ref(v_a_2889_);
v___x_2895_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2884_, v_a_2893_, v___x_2894_, v_a_2888_, v_a_2889_, v_a_2890_);
return v___x_2895_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec_ref(v_ext_2884_);
v_a_2896_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2892_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2892_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal___boxed(lean_object* v_ext_2904_, lean_object* v_fvar_2905_, lean_object* v_prio_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(v_ext_2904_, v_fvar_2905_, v_prio_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(uint8_t v_x_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___y_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed(lean_object* v_x_2916_, lean_object* v___y_2917_){
_start:
{
uint8_t v_x_31__boxed_2918_; lean_object* v_res_2919_; 
v_x_31__boxed_2918_ = lean_unbox(v_x_2916_);
v_res_2919_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(v_x_31__boxed_2918_, v___y_2917_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(lean_object* v___y_2920_){
_start:
{
lean_inc_ref(v___y_2920_);
return v___y_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed(lean_object* v___y_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(v___y_2921_);
lean_dec_ref(v___y_2921_);
return v_res_2922_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5(void){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_2929_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__6(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2);
v___x_2931_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
lean_ctor_set(v___x_2932_, 1, v___x_2930_);
return v___x_2932_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__7(void){
_start:
{
lean_object* v___f_2933_; lean_object* v___f_2934_; lean_object* v___x_2935_; lean_object* v___f_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___f_2933_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1));
v___f_2934_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2));
v___x_2935_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__6, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__6_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__6);
v___f_2936_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0));
v___x_2937_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4));
v___x_2938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___f_2936_);
lean_ctor_set(v___x_2938_, 2, v___x_2935_);
lean_ctor_set(v___x_2938_, 3, v___f_2934_);
lean_ctor_set(v___x_2938_, 4, v___f_2933_);
return v___x_2938_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt(void){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__7, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__7_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__7);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt;
v___x_2942_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2____boxed(lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg(lean_object* v_cls_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_options_2951_; uint8_t v_hasTrace_2952_; 
v_options_2951_ = lean_ctor_get(v___y_2949_, 2);
v_hasTrace_2952_ = lean_ctor_get_uint8(v_options_2951_, sizeof(void*)*1);
if (v_hasTrace_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec(v_cls_2948_);
v___x_2953_ = lean_box(v_hasTrace_2952_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
else
{
lean_object* v_inheritedTraceOptions_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_inheritedTraceOptions_2955_ = lean_ctor_get(v___y_2949_, 13);
v___x_2956_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg___closed__1));
v___x_2957_ = l_Lean_Name_append(v___x_2956_, v_cls_2948_);
v___x_2958_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2955_, v_options_2951_, v___x_2957_);
lean_dec(v___x_2957_);
v___x_2959_ = lean_box(v___x_2958_);
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg___boxed(lean_object* v_cls_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg(v_cls_2961_, v___y_2962_);
lean_dec_ref(v___y_2962_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(lean_object* v_cls_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg(v_cls_2965_, v___y_2968_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___boxed(lean_object* v_cls_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v_cls_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
return v_res_2978_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2980_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0));
v___x_2981_ = l_Lean_stringToMessageData(v___x_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(lean_object* v_____r_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1);
v___x_2989_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2988_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed(lean_object* v_____r_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(v_____r_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
return v_res_2996_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2997_; double v___x_2998_; 
v___x_2997_ = lean_unsigned_to_nat(0u);
v___x_2998_ = lean_float_of_nat(v___x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(lean_object* v_cls_3002_, lean_object* v_msg_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v_ref_3009_; lean_object* v___x_3010_; lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3055_; 
v_ref_3009_ = lean_ctor_get(v___y_3006_, 5);
v___x_3010_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3013_ = v___x_3010_;
v_isShared_3014_ = v_isSharedCheck_3055_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3055_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v_traceState_3016_; lean_object* v_env_3017_; lean_object* v_nextMacroScope_3018_; lean_object* v_ngen_3019_; lean_object* v_auxDeclNGen_3020_; lean_object* v_cache_3021_; lean_object* v_messages_3022_; lean_object* v_infoState_3023_; lean_object* v_snapshotTasks_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3054_; 
v___x_3015_ = lean_st_ref_take(v___y_3007_);
v_traceState_3016_ = lean_ctor_get(v___x_3015_, 4);
v_env_3017_ = lean_ctor_get(v___x_3015_, 0);
v_nextMacroScope_3018_ = lean_ctor_get(v___x_3015_, 1);
v_ngen_3019_ = lean_ctor_get(v___x_3015_, 2);
v_auxDeclNGen_3020_ = lean_ctor_get(v___x_3015_, 3);
v_cache_3021_ = lean_ctor_get(v___x_3015_, 5);
v_messages_3022_ = lean_ctor_get(v___x_3015_, 6);
v_infoState_3023_ = lean_ctor_get(v___x_3015_, 7);
v_snapshotTasks_3024_ = lean_ctor_get(v___x_3015_, 8);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3026_ = v___x_3015_;
v_isShared_3027_ = v_isSharedCheck_3054_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_snapshotTasks_3024_);
lean_inc(v_infoState_3023_);
lean_inc(v_messages_3022_);
lean_inc(v_cache_3021_);
lean_inc(v_traceState_3016_);
lean_inc(v_auxDeclNGen_3020_);
lean_inc(v_ngen_3019_);
lean_inc(v_nextMacroScope_3018_);
lean_inc(v_env_3017_);
lean_dec(v___x_3015_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3054_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
uint64_t v_tid_3028_; lean_object* v_traces_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3053_; 
v_tid_3028_ = lean_ctor_get_uint64(v_traceState_3016_, sizeof(void*)*1);
v_traces_3029_ = lean_ctor_get(v_traceState_3016_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_traceState_3016_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3031_ = v_traceState_3016_;
v_isShared_3032_ = v_isSharedCheck_3053_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_traces_3029_);
lean_dec(v_traceState_3016_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3053_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; double v___x_3034_; uint8_t v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
v___x_3033_ = lean_box(0);
v___x_3034_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__0);
v___x_3035_ = 0;
v___x_3036_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__1));
v___x_3037_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3037_, 0, v_cls_3002_);
lean_ctor_set(v___x_3037_, 1, v___x_3033_);
lean_ctor_set(v___x_3037_, 2, v___x_3036_);
lean_ctor_set_float(v___x_3037_, sizeof(void*)*3, v___x_3034_);
lean_ctor_set_float(v___x_3037_, sizeof(void*)*3 + 8, v___x_3034_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*3 + 16, v___x_3035_);
v___x_3038_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___closed__2));
v___x_3039_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set(v___x_3039_, 1, v_a_3011_);
lean_ctor_set(v___x_3039_, 2, v___x_3038_);
lean_inc(v_ref_3009_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v_ref_3009_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = l_Lean_PersistentArray_push___redArg(v_traces_3029_, v___x_3040_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3041_);
v___x_3043_ = v___x_3031_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3041_);
lean_ctor_set_uint64(v_reuseFailAlloc_3052_, sizeof(void*)*1, v_tid_3028_);
v___x_3043_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3045_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 4, v___x_3043_);
v___x_3045_ = v___x_3026_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_env_3017_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_nextMacroScope_3018_);
lean_ctor_set(v_reuseFailAlloc_3051_, 2, v_ngen_3019_);
lean_ctor_set(v_reuseFailAlloc_3051_, 3, v_auxDeclNGen_3020_);
lean_ctor_set(v_reuseFailAlloc_3051_, 4, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3051_, 5, v_cache_3021_);
lean_ctor_set(v_reuseFailAlloc_3051_, 6, v_messages_3022_);
lean_ctor_set(v_reuseFailAlloc_3051_, 7, v_infoState_3023_);
lean_ctor_set(v_reuseFailAlloc_3051_, 8, v_snapshotTasks_3024_);
v___x_3045_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3046_ = lean_st_ref_set(v___y_3007_, v___x_3045_);
v___x_3047_ = lean_box(0);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3047_);
v___x_3049_ = v___x_3013_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___boxed(lean_object* v_cls_3056_, lean_object* v_msg_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(v_cls_3056_, v_msg_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(lean_object* v_constName_3064_, uint8_t v_skipRealize_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v___x_3071_; lean_object* v_env_3072_; lean_object* v___x_3073_; 
v___x_3071_ = lean_st_ref_get(v___y_3069_);
v_env_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc_ref(v_env_3072_);
lean_dec(v___x_3071_);
lean_inc(v_constName_3064_);
v___x_3073_ = l_Lean_Environment_findAsync_x3f(v_env_3072_, v_constName_3064_, v_skipRealize_3065_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_3064_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
return v___x_3074_;
}
else
{
lean_object* v_val_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_constName_3064_);
v_val_3075_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3073_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_val_3075_);
lean_dec(v___x_3073_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set_tag(v___x_3077_, 0);
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_val_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0___boxed(lean_object* v_constName_3083_, lean_object* v_skipRealize_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
uint8_t v_skipRealize_boxed_3090_; lean_object* v_res_3091_; 
v_skipRealize_boxed_3090_ = lean_unbox(v_skipRealize_3084_);
v_res_3091_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_constName_3083_, v_skipRealize_boxed_3090_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
return v_res_3091_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3098_; uint64_t v___x_3099_; 
v___x_3098_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0));
v___x_3099_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3098_);
return v___x_3099_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1);
v___x_3101_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0));
v___x_3102_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
lean_ctor_set_uint64(v___x_3102_, sizeof(void*)*1, v___x_3100_);
return v___x_3102_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3103_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3);
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
return v___x_3105_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3106_ = lean_box(1);
v___x_3107_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_3108_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
lean_ctor_set(v___x_3109_, 1, v___x_3107_);
lean_ctor_set(v___x_3109_, 2, v___x_3106_);
return v___x_3109_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
lean_ctor_set(v___x_3114_, 2, v___x_3113_);
lean_ctor_set(v___x_3114_, 3, v___x_3112_);
lean_ctor_set(v___x_3114_, 4, v___x_3112_);
lean_ctor_set(v___x_3114_, 5, v___x_3112_);
lean_ctor_set(v___x_3114_, 6, v___x_3112_);
lean_ctor_set(v___x_3114_, 7, v___x_3112_);
lean_ctor_set(v___x_3114_, 8, v___x_3112_);
return v___x_3114_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3116_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
lean_ctor_set(v___x_3116_, 2, v___x_3115_);
lean_ctor_set(v___x_3116_, 3, v___x_3115_);
lean_ctor_set(v___x_3116_, 4, v___x_3115_);
lean_ctor_set(v___x_3116_, 5, v___x_3115_);
return v___x_3116_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_3118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
lean_ctor_set(v___x_3118_, 2, v___x_3117_);
lean_ctor_set(v___x_3118_, 3, v___x_3117_);
lean_ctor_set(v___x_3118_, 4, v___x_3117_);
return v___x_3118_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10));
v___x_3121_ = l_Lean_stringToMessageData(v___x_3120_);
return v___x_3121_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_3123_ = l_String_toRawSubstring_x27(v___x_3122_);
return v___x_3123_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15(void){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Array_mkArray0(lean_box(0));
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(lean_object* v___x_3130_, lean_object* v_ext_3131_, lean_object* v___x_3132_, lean_object* v___x_3133_, lean_object* v___x_3134_, lean_object* v___f_3135_, lean_object* v___x_3136_, lean_object* v_declName_3137_, lean_object* v_stx_3138_, uint8_t v_attrKind_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v___x_3143_; uint8_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3143_ = 0;
v___x_3144_ = 1;
v___x_3145_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2);
v___x_3146_ = lean_unsigned_to_nat(0u);
v___x_3147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_3148_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5);
v___x_3149_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6));
v___x_3150_ = lean_box(0);
lean_inc(v___x_3130_);
v___x_3151_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3151_, 0, v___x_3145_);
lean_ctor_set(v___x_3151_, 1, v___x_3130_);
lean_ctor_set(v___x_3151_, 2, v___x_3148_);
lean_ctor_set(v___x_3151_, 3, v___x_3149_);
lean_ctor_set(v___x_3151_, 4, v___x_3150_);
lean_ctor_set(v___x_3151_, 5, v___x_3146_);
lean_ctor_set(v___x_3151_, 6, v___x_3150_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*7, v___x_3143_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*7 + 1, v___x_3143_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*7 + 2, v___x_3143_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*7 + 3, v___x_3144_);
v___x_3152_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7);
v___x_3153_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8);
v___x_3154_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9);
v___x_3155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3152_);
lean_ctor_set(v___x_3155_, 1, v___x_3153_);
lean_ctor_set(v___x_3155_, 2, v___x_3130_);
lean_ctor_set(v___x_3155_, 3, v___x_3147_);
lean_ctor_set(v___x_3155_, 4, v___x_3154_);
v___x_3156_ = lean_st_mk_ref(v___x_3155_);
lean_inc(v_declName_3137_);
v___x_3157_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_declName_3137_, v___x_3143_, v___x_3151_, v___x_3156_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec_ref(v___x_3157_);
v___x_3158_ = lean_unsigned_to_nat(1u);
v___x_3159_ = l_Lean_Syntax_getArg(v_stx_3138_, v___x_3158_);
lean_inc(v___x_3159_);
v___x_3160_ = l_Lean_getAttrParamOptPrio(v___x_3159_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3250_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3250_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3250_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___y_3172_; lean_object* v___y_3174_; lean_object* v___y_3175_; uint8_t v___y_3176_; lean_object* v___x_3189_; 
v___x_3165_ = lean_box(0);
lean_inc(v_declName_3137_);
v___x_3189_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(v_ext_3131_, v_declName_3137_, v_a_3161_, v_attrKind_3139_, v___x_3151_, v___x_3156_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_dec(v___x_3159_);
lean_dec_ref(v___x_3151_);
lean_dec_ref(v___y_3140_);
lean_dec(v_declName_3137_);
lean_dec_ref(v___x_3136_);
lean_dec_ref(v___f_3135_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v___x_3132_);
v___y_3172_ = v___x_3189_;
goto v___jp_3171_;
}
else
{
lean_object* v_a_3190_; uint8_t v___y_3192_; uint8_t v___x_3248_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
v___x_3248_ = l_Lean_Exception_isInterrupt(v_a_3190_);
if (v___x_3248_ == 0)
{
uint8_t v___x_3249_; 
v___x_3249_ = l_Lean_Exception_isRuntime(v_a_3190_);
v___y_3192_ = v___x_3249_;
goto v___jp_3191_;
}
else
{
lean_dec(v_a_3190_);
v___y_3192_ = v___x_3248_;
goto v___jp_3191_;
}
v___jp_3191_:
{
if (v___y_3192_ == 0)
{
lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3246_; 
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3246_ == 0)
{
lean_object* v_unused_3247_; 
v_unused_3247_ = lean_ctor_get(v___x_3189_, 0);
lean_dec(v_unused_3247_);
v___x_3194_ = v___x_3189_;
v_isShared_3195_ = v_isSharedCheck_3246_;
goto v_resetjp_3193_;
}
else
{
lean_dec(v___x_3189_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3246_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_3197_ = l_Lean_getBuiltinAttributeImpl(v___x_3196_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v_ref_3199_; lean_object* v_quotContext_3200_; lean_object* v_currMacroScope_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v_add_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3228_; 
lean_del_object(v___x_3194_);
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref(v___x_3197_);
v_ref_3199_ = lean_ctor_get(v___y_3140_, 5);
v_quotContext_3200_ = lean_ctor_get(v___y_3140_, 10);
v_currMacroScope_3201_ = lean_ctor_get(v___y_3140_, 11);
v___x_3202_ = l_Lean_SourceInfo_fromRef(v_ref_3199_, v___y_3192_);
v___x_3203_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12);
lean_inc(v_currMacroScope_3201_);
lean_inc(v_quotContext_3200_);
v___x_3204_ = l_Lean_addMacroScope(v_quotContext_3200_, v___x_3196_, v_currMacroScope_3201_);
v___x_3205_ = lean_box(0);
lean_inc(v___x_3202_);
v___x_3206_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3202_);
lean_ctor_set(v___x_3206_, 1, v___x_3203_);
lean_ctor_set(v___x_3206_, 2, v___x_3204_);
lean_ctor_set(v___x_3206_, 3, v___x_3205_);
v_add_3207_ = lean_ctor_get(v_a_3198_, 1);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_a_3198_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; lean_object* v_unused_3230_; 
v_unused_3229_ = lean_ctor_get(v_a_3198_, 2);
lean_dec(v_unused_3229_);
v_unused_3230_ = lean_ctor_get(v_a_3198_, 0);
lean_dec(v_unused_3230_);
v___x_3209_ = v_a_3198_;
v_isShared_3210_ = v_isSharedCheck_3228_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_add_3207_);
lean_dec(v_a_3198_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3228_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3211_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14));
v___x_3212_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15);
lean_inc(v___x_3202_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 1);
lean_ctor_set(v___x_3209_, 2, v___x_3212_);
lean_ctor_set(v___x_3209_, 1, v___x_3211_);
lean_ctor_set(v___x_3209_, 0, v___x_3202_);
v___x_3214_ = v___x_3209_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3215_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16));
v___x_3216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3217_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17));
v___x_3218_ = l_Lean_Name_mkStr4(v___x_3136_, v___x_3215_, v___x_3216_, v___x_3217_);
v___x_3219_ = l_Lean_Syntax_node2(v___x_3202_, v___x_3218_, v___x_3206_, v___x_3214_);
v___x_3220_ = lean_unsigned_to_nat(3u);
v___x_3221_ = l_Lean_Syntax_setArg(v___x_3219_, v___x_3220_, v___x_3159_);
v___x_3222_ = lean_box(v_attrKind_3139_);
lean_inc(v___y_3141_);
lean_inc_ref(v___y_3140_);
v___x_3223_ = lean_apply_6(v_add_3207_, v_declName_3137_, v___x_3221_, v___x_3222_, v___y_3140_, v___y_3141_, lean_box(0));
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_dec_ref(v___x_3223_);
lean_dec_ref(v___x_3151_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v___f_3135_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v___x_3132_);
goto v___jp_3166_;
}
else
{
lean_object* v_a_3224_; uint8_t v___x_3225_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
v___x_3225_ = l_Lean_Exception_isInterrupt(v_a_3224_);
if (v___x_3225_ == 0)
{
uint8_t v___x_3226_; 
lean_inc(v_a_3224_);
v___x_3226_ = l_Lean_Exception_isRuntime(v_a_3224_);
v___y_3174_ = v___x_3223_;
v___y_3175_ = v_a_3224_;
v___y_3176_ = v___x_3226_;
goto v___jp_3173_;
}
else
{
v___y_3174_ = v___x_3223_;
v___y_3175_ = v_a_3224_;
v___y_3176_ = v___x_3225_;
goto v___jp_3173_;
}
}
}
}
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3245_; 
lean_del_object(v___x_3163_);
lean_dec(v___x_3159_);
lean_dec(v___x_3156_);
lean_dec_ref(v___x_3151_);
lean_dec(v_declName_3137_);
lean_dec_ref(v___x_3136_);
lean_dec_ref(v___f_3135_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v___x_3132_);
v_a_3231_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3233_ = v___x_3197_;
v_isShared_3234_ = v_isSharedCheck_3245_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3197_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3245_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_ref_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v_ref_3235_ = lean_ctor_get(v___y_3140_, 5);
lean_inc(v_ref_3235_);
lean_dec_ref(v___y_3140_);
v___x_3236_ = lean_io_error_to_string(v_a_3231_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set_tag(v___x_3194_, 3);
lean_ctor_set(v___x_3194_, 0, v___x_3236_);
v___x_3238_ = v___x_3194_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3239_ = l_Lean_MessageData_ofFormat(v___x_3238_);
v___x_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3240_, 0, v_ref_3235_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v___x_3240_);
v___x_3242_ = v___x_3233_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3159_);
lean_dec_ref(v___x_3151_);
lean_dec_ref(v___y_3140_);
lean_dec(v_declName_3137_);
lean_dec_ref(v___x_3136_);
lean_dec_ref(v___f_3135_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v___x_3132_);
v___y_3172_ = v___x_3189_;
goto v___jp_3171_;
}
}
}
v___jp_3166_:
{
lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3167_ = lean_st_ref_get(v___x_3156_);
lean_dec(v___x_3156_);
lean_dec(v___x_3167_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3169_ = v___x_3163_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3165_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
v___jp_3171_:
{
if (lean_obj_tag(v___y_3172_) == 0)
{
lean_dec_ref(v___y_3172_);
goto v___jp_3166_;
}
else
{
lean_del_object(v___x_3163_);
lean_dec(v___x_3156_);
return v___y_3172_;
}
}
v___jp_3173_:
{
if (v___y_3176_ == 0)
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v_a_3180_; uint8_t v___x_3181_; 
lean_dec_ref(v___y_3174_);
v___x_3177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3178_ = l_Lean_Name_mkStr4(v___x_3132_, v___x_3133_, v___x_3134_, v___x_3177_);
lean_inc(v___x_3178_);
v___x_3179_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___redArg(v___x_3178_, v___y_3140_);
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3179_);
v___x_3181_ = lean_unbox(v_a_3180_);
lean_dec(v_a_3180_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; 
lean_dec(v___x_3178_);
lean_dec_ref(v___y_3175_);
lean_inc(v___y_3141_);
lean_inc(v___x_3156_);
v___x_3182_ = lean_apply_6(v___f_3135_, v___x_3165_, v___x_3151_, v___x_3156_, v___y_3140_, v___y_3141_, lean_box(0));
v___y_3172_ = v___x_3182_;
goto v___jp_3171_;
}
else
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3183_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11);
v___x_3184_ = l_Lean_Exception_toMessageData(v___y_3175_);
v___x_3185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(v___x_3178_, v___x_3185_, v___x_3151_, v___x_3156_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; lean_object* v___x_3188_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref(v___x_3186_);
lean_inc(v___y_3141_);
lean_inc(v___x_3156_);
v___x_3188_ = lean_apply_6(v___f_3135_, v_a_3187_, v___x_3151_, v___x_3156_, v___y_3140_, v___y_3141_, lean_box(0));
v___y_3172_ = v___x_3188_;
goto v___jp_3171_;
}
else
{
lean_dec_ref(v___x_3151_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v___f_3135_);
v___y_3172_ = v___x_3186_;
goto v___jp_3171_;
}
}
}
else
{
lean_dec_ref(v___y_3175_);
lean_del_object(v___x_3163_);
lean_dec(v___x_3156_);
lean_dec_ref(v___x_3151_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v___f_3135_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v___x_3132_);
return v___y_3174_;
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v___x_3159_);
lean_dec(v___x_3156_);
lean_dec_ref(v___x_3151_);
lean_dec_ref(v___y_3140_);
lean_dec(v_declName_3137_);
lean_dec_ref(v___x_3136_);
lean_dec_ref(v___f_3135_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v___x_3132_);
lean_dec_ref(v_ext_3131_);
v_a_3251_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3160_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3160_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v___x_3156_);
lean_dec_ref(v___x_3151_);
lean_dec_ref(v___y_3140_);
lean_dec(v_declName_3137_);
lean_dec_ref(v___x_3136_);
lean_dec_ref(v___f_3135_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v___x_3132_);
lean_dec_ref(v_ext_3131_);
v_a_3259_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3157_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3157_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed(lean_object* v___x_3267_, lean_object* v_ext_3268_, lean_object* v___x_3269_, lean_object* v___x_3270_, lean_object* v___x_3271_, lean_object* v___f_3272_, lean_object* v___x_3273_, lean_object* v_declName_3274_, lean_object* v_stx_3275_, lean_object* v_attrKind_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
uint8_t v_attrKind_boxed_3280_; lean_object* v_res_3281_; 
v_attrKind_boxed_3280_ = lean_unbox(v_attrKind_3276_);
v_res_3281_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(v___x_3267_, v_ext_3268_, v___x_3269_, v___x_3270_, v___x_3271_, v___f_3272_, v___x_3273_, v_declName_3274_, v_stx_3275_, v_attrKind_boxed_3280_, v___y_3277_, v___y_3278_);
lean_dec(v___y_3278_);
lean_dec(v_stx_3275_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3_spec__3(lean_object* v_msgData_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___x_3286_; lean_object* v_env_3287_; lean_object* v_options_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3286_ = lean_st_ref_get(v___y_3284_);
v_env_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc_ref(v_env_3287_);
lean_dec(v___x_3286_);
v_options_3288_ = lean_ctor_get(v___y_3283_, 2);
v___x_3289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_3290_ = lean_unsigned_to_nat(32u);
v___x_3291_ = lean_mk_empty_array_with_capacity(v___x_3290_);
lean_dec_ref(v___x_3291_);
v___x_3292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
lean_inc_ref(v_options_3288_);
v___x_3293_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3293_, 0, v_env_3287_);
lean_ctor_set(v___x_3293_, 1, v___x_3289_);
lean_ctor_set(v___x_3293_, 2, v___x_3292_);
lean_ctor_set(v___x_3293_, 3, v_options_3288_);
v___x_3294_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v_msgData_3282_);
v___x_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3_spec__3___boxed(lean_object* v_msgData_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3_spec__3(v_msgData_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3___redArg(lean_object* v_msg_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v_ref_3305_; lean_object* v___x_3306_; lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3315_; 
v_ref_3305_ = lean_ctor_get(v___y_3302_, 5);
v___x_3306_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3_spec__3(v_msg_3301_, v___y_3302_, v___y_3303_);
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
lean_inc(v_ref_3305_);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v_ref_3305_);
lean_ctor_set(v___x_3311_, 1, v_a_3307_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set_tag(v___x_3309_, 1);
lean_ctor_set(v___x_3309_, 0, v___x_3311_);
v___x_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3___redArg___boxed(lean_object* v_msg_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3___redArg(v_msg_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
return v_res_3320_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0));
v___x_3323_ = l_Lean_stringToMessageData(v___x_3322_);
return v___x_3323_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2));
v___x_3326_ = l_Lean_stringToMessageData(v___x_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(lean_object* v___x_3327_, lean_object* v_decl_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3332_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1);
v___x_3333_ = l_Lean_MessageData_ofName(v___x_3327_);
v___x_3334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3___redArg(v___x_3336_, v___y_3329_, v___y_3330_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed(lean_object* v___x_3338_, lean_object* v_decl_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(v___x_3338_, v_decl_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v_decl_3339_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(lean_object* v_ext_3364_){
_start:
{
lean_object* v___f_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___f_3371_; lean_object* v___f_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___f_3365_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0));
v___x_3366_ = lean_box(1);
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_3370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___f_3371_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3371_, 0, v___x_3366_);
lean_closure_set(v___f_3371_, 1, v_ext_3364_);
lean_closure_set(v___f_3371_, 2, v___x_3368_);
lean_closure_set(v___f_3371_, 3, v___x_3369_);
lean_closure_set(v___f_3371_, 4, v___x_3370_);
lean_closure_set(v___f_3371_, 5, v___f_3365_);
lean_closure_set(v___f_3371_, 6, v___x_3367_);
v___f_3372_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5));
v___x_3373_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7));
v___x_3374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v___f_3371_);
lean_ctor_set(v___x_3374_, 2, v___f_3372_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3(lean_object* v_00_u03b1_3375_, lean_object* v_msg_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3___redArg(v_msg_3376_, v___y_3377_, v___y_3378_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3___boxed(lean_object* v_00_u03b1_3381_, lean_object* v_msg_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__3(v_00_u03b1_3381_, v_msg_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
return v_res_3386_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
v___x_3388_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(v___x_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_);
v___x_3391_ = l_Lean_registerBuiltinAttribute(v___x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2____boxed(lean_object* v_a_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(lean_object* v_ext_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v___x_3397_; lean_object* v_ext_3398_; lean_object* v_toEnvExtension_3399_; lean_object* v_env_3400_; lean_object* v_asyncMode_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3397_ = lean_st_ref_get(v_a_3395_);
v_ext_3398_ = lean_ctor_get(v_ext_3394_, 1);
v_toEnvExtension_3399_ = lean_ctor_get(v_ext_3398_, 0);
v_env_3400_ = lean_ctor_get(v___x_3397_, 0);
lean_inc_ref(v_env_3400_);
lean_dec(v___x_3397_);
v_asyncMode_3401_ = lean_ctor_get(v_toEnvExtension_3399_, 2);
v___x_3402_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
v___x_3403_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3402_, v_ext_3394_, v_env_3400_, v_asyncMode_3401_);
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg___boxed(lean_object* v_ext_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_3405_, v_a_3406_);
lean_dec(v_a_3406_);
lean_dec_ref(v_ext_3405_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(lean_object* v_ext_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_3409_, v_a_3411_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___boxed(lean_object* v_ext_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(v_ext_3414_, v_a_3415_, v_a_3416_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3415_);
lean_dec_ref(v_ext_3414_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(lean_object* v_a_3419_){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
v___x_3422_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v___x_3421_, v_a_3419_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg___boxed(lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3423_);
lean_dec(v_a_3423_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3427_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___boxed(lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_(lean_object* v_x_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_box(0);
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2____boxed(lean_object* v_x_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_(v_x_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v_x_3440_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; uint8_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___f_3459_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_));
v___x_3460_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_));
v___x_3461_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_));
v___x_3462_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_));
v___x_3463_ = 0;
v___x_3464_ = lean_box(2);
v___x_3465_ = l_Lean_registerTagAttribute(v___x_3460_, v___x_3461_, v___f_3459_, v___x_3462_, v___x_3463_, v___x_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2____boxed(lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_();
return v_res_3467_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isMVCGenInvariantType(lean_object* v_env_3468_, lean_object* v_ty_3469_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_Expr_getAppFn(v_ty_3469_);
if (lean_obj_tag(v___x_3470_) == 4)
{
lean_object* v_declName_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v_declName_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_declName_3471_);
lean_dec_ref(v___x_3470_);
v___x_3472_ = l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenInvariantAttr;
v___x_3473_ = l_Lean_TagAttribute_hasTag(v___x_3472_, v_env_3468_, v_declName_3471_);
return v___x_3473_;
}
else
{
uint8_t v___x_3474_; 
lean_dec_ref(v___x_3470_);
lean_dec_ref(v_env_3468_);
v___x_3474_ = 0;
return v___x_3474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_isMVCGenInvariantType___boxed(lean_object* v_env_3475_, lean_object* v_ty_3476_){
_start:
{
uint8_t v_res_3477_; lean_object* v_r_3478_; 
v_res_3477_ = l_Lean_Elab_Tactic_Do_SpecAttr_isMVCGenInvariantType(v_env_3475_, v_ty_3476_);
lean_dec_ref(v_ty_3476_);
v_r_3478_ = lean_box(v_res_3477_);
return v_r_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___f_3492_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_));
v___x_3493_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_));
v___x_3494_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_));
v___x_3495_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_));
v___x_3496_ = 0;
v___x_3497_ = lean_box(2);
v___x_3498_ = l_Lean_registerTagAttribute(v___x_3493_, v___x_3494_, v___f_3492_, v___x_3495_, v___x_3496_, v___x_3497_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2____boxed(lean_object* v_a_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_();
return v_res_3500_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isMVCGenWitnessType(lean_object* v_env_3501_, lean_object* v_ty_3502_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Expr_getAppFn(v_ty_3502_);
if (lean_obj_tag(v___x_3503_) == 4)
{
lean_object* v_declName_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v_declName_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_declName_3504_);
lean_dec_ref(v___x_3503_);
v___x_3505_ = l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenWitnessTypeAttr;
v___x_3506_ = l_Lean_TagAttribute_hasTag(v___x_3505_, v_env_3501_, v_declName_3504_);
return v___x_3506_;
}
else
{
uint8_t v___x_3507_; 
lean_dec_ref(v___x_3503_);
lean_dec_ref(v_env_3501_);
v___x_3507_ = 0;
return v___x_3507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_isMVCGenWitnessType___boxed(lean_object* v_env_3508_, lean_object* v_ty_3509_){
_start:
{
uint8_t v_res_3510_; lean_object* v_r_3511_; 
v_res_3510_ = l_Lean_Elab_Tactic_Do_SpecAttr_isMVCGenWitnessType(v_env_3508_, v_ty_3509_);
lean_dec_ref(v_ty_3509_);
v_r_3511_ = lean_box(v_res_3510_);
return v_r_3511_;
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
res = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2603982925____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenInvariantAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenInvariantAttr);
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3101451261____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenWitnessTypeAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenWitnessTypeAttr);
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
