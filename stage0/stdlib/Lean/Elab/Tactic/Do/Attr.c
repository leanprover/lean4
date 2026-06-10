// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Attr
// Imports: public import Lean.Meta.Tactic.Simp public import Lean.Meta.Sym.Pattern public import Std.Tactic.Do.Syntax public import Std.Internal.Do.Triple.Basic import Init.While import Init.Syntax import Lean.Meta.Sym.Simp.DiscrTree
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
lean_object* l_Lean_Meta_Simp_Context_mkDefault___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessExprPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_range(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_instInhabitedPattern_default;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ofOrigin(lean_object*);
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
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_triple_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_triple_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_simp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_simp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheoremKind_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheoremKind;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_global_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_global_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_local_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_local_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_stx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_stx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecProof_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecProof_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecProof_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecProof_default = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecProof_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecProof = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecProof_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ofOrigin(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_getProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rel_wp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(63, 136, 191, 100, 189, 54, 237, 105)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_instantiate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_instantiate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instToMessageDataSpecProof___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instToMessageDataSpecProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instToMessageDataSpecProof___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instToMessageDataSpecProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instToMessageDataSpecProof___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instToMessageDataSpecProof = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instToMessageDataSpecProof___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems;
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_sym_prune"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 115, 37, 193, 53, 26, 158, 206)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__5(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__7(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 6, 42, 106, 0, 77, 75, 237)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 60, .m_data = "unexpected kind of spec theorem; expected `Triple` or `⊑ wp`"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___closed__0_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 43, .m_data = "invalid 'spec', expected `Triple` or `⊑ wp`"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "internalSpecMap"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__3_value),LEAN_SCALAR_PTR_LITERAL(22, 5, 253, 175, 168, 41, 171, 42)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486626____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486626____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_specAttr;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed, .m_arity = 12, .m_num_fixed = 6, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mkSpecAttr"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 109, 122, 82, 215, 148, 2, 116)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(131, 130, 97, 217, 238, 242, 98, 155)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "spec"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 105, 220, 149, 84, 64, 243, 129)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "Marks Hoare triple specifications and simp theorems for use with `mvcgen` tactics"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3903886647____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3903886647____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ofOrigin(lean_object* v_x_212_){
_start:
{
switch(lean_obj_tag(v_x_212_))
{
case 0:
{
lean_object* v_declName_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_declName_213_ = lean_ctor_get(v_x_212_, 0);
lean_inc(v_declName_213_);
lean_dec_ref_known(v_x_212_, 1);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v_declName_213_);
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
case 1:
{
lean_object* v_fvarId_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_224_; 
v_fvarId_216_ = lean_ctor_get(v_x_212_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v_x_212_);
if (v_isSharedCheck_224_ == 0)
{
v___x_218_ = v_x_212_;
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_fvarId_216_);
lean_dec(v_x_212_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_fvarId_216_);
v___x_221_ = v_reuseFailAlloc_223_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
}
default: 
{
lean_object* v___x_225_; 
lean_dec_ref(v_x_212_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
if (lean_obj_tag(v_a_226_) == 0)
{
lean_object* v___x_228_; 
v___x_228_ = l_List_reverse___redArg(v_a_227_);
return v___x_228_;
}
else
{
lean_object* v_head_229_; lean_object* v_tail_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_239_; 
v_head_229_ = lean_ctor_get(v_a_226_, 0);
v_tail_230_ = lean_ctor_get(v_a_226_, 1);
v_isSharedCheck_239_ = !lean_is_exclusive(v_a_226_);
if (v_isSharedCheck_239_ == 0)
{
v___x_232_ = v_a_226_;
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_tail_230_);
lean_inc(v_head_229_);
lean_dec(v_a_226_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = l_Lean_mkLevelParam(v_head_229_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v_a_227_);
lean_ctor_set(v___x_232_, 0, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_a_227_);
v___x_236_ = v_reuseFailAlloc_238_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
v_a_226_ = v_tail_230_;
v_a_227_ = v___x_236_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; lean_object* v_env_247_; lean_object* v___x_248_; lean_object* v_mctx_249_; lean_object* v_lctx_250_; lean_object* v_options_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_246_ = lean_st_ref_get(v___y_244_);
v_env_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc_ref(v_env_247_);
lean_dec(v___x_246_);
v___x_248_ = lean_st_ref_get(v___y_242_);
v_mctx_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc_ref(v_mctx_249_);
lean_dec(v___x_248_);
v_lctx_250_ = lean_ctor_get(v___y_241_, 2);
v_options_251_ = lean_ctor_get(v___y_243_, 2);
lean_inc_ref(v_options_251_);
lean_inc_ref(v_lctx_250_);
v___x_252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_252_, 0, v_env_247_);
lean_ctor_set(v___x_252_, 1, v_mctx_249_);
lean_ctor_set(v___x_252_, 2, v_lctx_250_);
lean_ctor_set(v___x_252_, 3, v_options_251_);
v___x_253_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v_msgData_240_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msgData_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_ref_268_; lean_object* v___x_269_; lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_278_; 
v_ref_268_ = lean_ctor_get(v___y_265_, 5);
v___x_269_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_278_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
lean_inc(v_ref_268_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_ref_268_);
lean_ctor_set(v___x_274_, 1, v_a_270_);
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 1);
lean_ctor_set(v___x_272_, 0, v___x_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_286_, lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_fileName_293_; lean_object* v_fileMap_294_; lean_object* v_options_295_; lean_object* v_currRecDepth_296_; lean_object* v_maxRecDepth_297_; lean_object* v_ref_298_; lean_object* v_currNamespace_299_; lean_object* v_openDecls_300_; lean_object* v_initHeartbeats_301_; lean_object* v_maxHeartbeats_302_; lean_object* v_quotContext_303_; lean_object* v_currMacroScope_304_; uint8_t v_diag_305_; lean_object* v_cancelTk_x3f_306_; uint8_t v_suppressElabErrors_307_; lean_object* v_inheritedTraceOptions_308_; lean_object* v_ref_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_fileName_293_ = lean_ctor_get(v___y_290_, 0);
v_fileMap_294_ = lean_ctor_get(v___y_290_, 1);
v_options_295_ = lean_ctor_get(v___y_290_, 2);
v_currRecDepth_296_ = lean_ctor_get(v___y_290_, 3);
v_maxRecDepth_297_ = lean_ctor_get(v___y_290_, 4);
v_ref_298_ = lean_ctor_get(v___y_290_, 5);
v_currNamespace_299_ = lean_ctor_get(v___y_290_, 6);
v_openDecls_300_ = lean_ctor_get(v___y_290_, 7);
v_initHeartbeats_301_ = lean_ctor_get(v___y_290_, 8);
v_maxHeartbeats_302_ = lean_ctor_get(v___y_290_, 9);
v_quotContext_303_ = lean_ctor_get(v___y_290_, 10);
v_currMacroScope_304_ = lean_ctor_get(v___y_290_, 11);
v_diag_305_ = lean_ctor_get_uint8(v___y_290_, sizeof(void*)*14);
v_cancelTk_x3f_306_ = lean_ctor_get(v___y_290_, 12);
v_suppressElabErrors_307_ = lean_ctor_get_uint8(v___y_290_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_308_ = lean_ctor_get(v___y_290_, 13);
v_ref_309_ = l_Lean_replaceRef(v_ref_286_, v_ref_298_);
lean_inc_ref(v_inheritedTraceOptions_308_);
lean_inc(v_cancelTk_x3f_306_);
lean_inc(v_currMacroScope_304_);
lean_inc(v_quotContext_303_);
lean_inc(v_maxHeartbeats_302_);
lean_inc(v_initHeartbeats_301_);
lean_inc(v_openDecls_300_);
lean_inc(v_currNamespace_299_);
lean_inc(v_maxRecDepth_297_);
lean_inc(v_currRecDepth_296_);
lean_inc_ref(v_options_295_);
lean_inc_ref(v_fileMap_294_);
lean_inc_ref(v_fileName_293_);
v___x_310_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_310_, 0, v_fileName_293_);
lean_ctor_set(v___x_310_, 1, v_fileMap_294_);
lean_ctor_set(v___x_310_, 2, v_options_295_);
lean_ctor_set(v___x_310_, 3, v_currRecDepth_296_);
lean_ctor_set(v___x_310_, 4, v_maxRecDepth_297_);
lean_ctor_set(v___x_310_, 5, v_ref_309_);
lean_ctor_set(v___x_310_, 6, v_currNamespace_299_);
lean_ctor_set(v___x_310_, 7, v_openDecls_300_);
lean_ctor_set(v___x_310_, 8, v_initHeartbeats_301_);
lean_ctor_set(v___x_310_, 9, v_maxHeartbeats_302_);
lean_ctor_set(v___x_310_, 10, v_quotContext_303_);
lean_ctor_set(v___x_310_, 11, v_currMacroScope_304_);
lean_ctor_set(v___x_310_, 12, v_cancelTk_x3f_306_);
lean_ctor_set(v___x_310_, 13, v_inheritedTraceOptions_308_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*14, v_diag_305_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*14 + 1, v_suppressElabErrors_307_);
v___x_311_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_287_, v___y_288_, v___y_289_, v___x_310_, v___y_291_);
lean_dec_ref_known(v___x_310_, 14);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_312_, lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_312_, v_msg_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v_ref_312_);
return v_res_319_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_320_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
lean_ctor_set(v___x_325_, 2, v___x_324_);
lean_ctor_set(v___x_325_, 3, v___x_324_);
lean_ctor_set(v___x_325_, 4, v___x_323_);
lean_ctor_set(v___x_325_, 5, v___x_323_);
lean_ctor_set(v___x_325_, 6, v___x_323_);
lean_ctor_set(v___x_325_, 7, v___x_323_);
lean_ctor_set(v___x_325_, 8, v___x_323_);
lean_ctor_set(v___x_325_, 9, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_unsigned_to_nat(32u);
v___x_327_ = lean_mk_empty_array_with_capacity(v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_329_ = ((size_t)5ULL);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_unsigned_to_nat(32u);
v___x_332_ = lean_mk_empty_array_with_capacity(v___x_331_);
v___x_333_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_334_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_332_);
lean_ctor_set(v___x_334_, 2, v___x_330_);
lean_ctor_set(v___x_334_, 3, v___x_330_);
lean_ctor_set_usize(v___x_334_, 4, v___x_329_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = lean_box(1);
v___x_336_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_337_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
lean_ctor_set(v___x_338_, 2, v___x_335_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_347_ = l_Lean_stringToMessageData(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_360_, lean_object* v_declHint_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; lean_object* v_env_365_; uint8_t v___x_366_; 
v___x_364_ = lean_st_ref_get(v___y_362_);
v_env_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_env_365_);
lean_dec(v___x_364_);
v___x_366_ = l_Lean_Name_isAnonymous(v_declHint_361_);
if (v___x_366_ == 0)
{
uint8_t v_isExporting_367_; 
v_isExporting_367_ = lean_ctor_get_uint8(v_env_365_, sizeof(void*)*8);
if (v_isExporting_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec_ref(v_env_365_);
lean_dec(v_declHint_361_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v_msg_360_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; uint8_t v___x_370_; 
lean_inc_ref(v_env_365_);
v___x_369_ = l_Lean_Environment_setExporting(v_env_365_, v___x_366_);
lean_inc(v_declHint_361_);
lean_inc_ref(v___x_369_);
v___x_370_ = l_Lean_Environment_contains(v___x_369_, v_declHint_361_, v_isExporting_367_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec_ref(v___x_369_);
lean_dec_ref(v_env_365_);
lean_dec(v_declHint_361_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v_msg_360_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_c_377_; lean_object* v___x_378_; 
v___x_372_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_374_ = l_Lean_Options_empty;
v___x_375_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_375_, 0, v___x_369_);
lean_ctor_set(v___x_375_, 1, v___x_372_);
lean_ctor_set(v___x_375_, 2, v___x_373_);
lean_ctor_set(v___x_375_, 3, v___x_374_);
lean_inc(v_declHint_361_);
v___x_376_ = l_Lean_MessageData_ofConstName(v_declHint_361_, v___x_366_);
v_c_377_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_377_, 0, v___x_375_);
lean_ctor_set(v_c_377_, 1, v___x_376_);
v___x_378_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_365_, v_declHint_361_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec_ref(v_env_365_);
lean_dec(v_declHint_361_);
v___x_379_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v_c_377_);
v___x_381_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = l_Lean_MessageData_note(v___x_382_);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v_msg_360_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
else
{
lean_object* v_val_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_421_; 
v_val_386_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_421_ == 0)
{
v___x_388_ = v___x_378_;
v_isShared_389_ = v_isSharedCheck_421_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_val_386_);
lean_dec(v___x_378_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_421_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_mod_393_; uint8_t v___x_394_; 
v___x_390_ = lean_box(0);
v___x_391_ = l_Lean_Environment_header(v_env_365_);
lean_dec_ref(v_env_365_);
v___x_392_ = l_Lean_EnvironmentHeader_moduleNames(v___x_391_);
v_mod_393_ = lean_array_get(v___x_390_, v___x_392_, v_val_386_);
lean_dec(v_val_386_);
lean_dec_ref(v___x_392_);
v___x_394_ = l_Lean_isPrivateName(v_declHint_361_);
lean_dec(v_declHint_361_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_395_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_c_377_);
v___x_397_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = l_Lean_MessageData_ofName(v_mod_393_);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_MessageData_note(v___x_402_);
v___x_404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_404_, 0, v_msg_360_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
if (v_isShared_389_ == 0)
{
lean_ctor_set_tag(v___x_388_, 0);
lean_ctor_set(v___x_388_, 0, v___x_404_);
v___x_406_ = v___x_388_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_408_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_c_377_);
v___x_410_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = l_Lean_MessageData_ofName(v_mod_393_);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = l_Lean_MessageData_note(v___x_415_);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v_msg_360_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
if (v_isShared_389_ == 0)
{
lean_ctor_set_tag(v___x_388_, 0);
lean_ctor_set(v___x_388_, 0, v___x_417_);
v___x_419_ = v___x_388_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_422_; 
lean_dec_ref(v_env_365_);
lean_dec(v_declHint_361_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_msg_360_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_423_, lean_object* v_declHint_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_423_, v_declHint_424_, v___y_425_);
lean_dec(v___y_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_428_, lean_object* v_declHint_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_445_; 
v___x_435_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_428_, v_declHint_429_, v___y_433_);
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_445_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = l_Lean_unknownIdentifierMessageTag;
v___x_441_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v_a_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_446_, lean_object* v_declHint_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_446_, v_declHint_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_454_, lean_object* v_msg_455_, lean_object* v_declHint_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; lean_object* v_a_463_; lean_object* v___x_464_; 
v___x_462_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_455_, v_declHint_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v___x_462_);
v___x_464_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_454_, v_a_463_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_465_, lean_object* v_msg_466_, lean_object* v_declHint_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_465_, v_msg_466_, v_declHint_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v_ref_465_);
return v_res_473_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_476_ = l_Lean_stringToMessageData(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_480_, lean_object* v_constName_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_487_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_488_ = 0;
lean_inc(v_constName_481_);
v___x_489_ = l_Lean_MessageData_ofConstName(v_constName_481_, v___x_488_);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_487_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_480_, v___x_492_, v_constName_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_494_, lean_object* v_constName_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_494_, v_constName_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v_ref_494_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(lean_object* v_constName_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_ref_508_; lean_object* v___x_509_; 
v_ref_508_ = lean_ctor_get(v___y_505_, 5);
v___x_509_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_508_, v_constName_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg___boxed(lean_object* v_constName_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(lean_object* v_constName_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; lean_object* v_env_524_; uint8_t v___x_525_; lean_object* v___x_526_; 
v___x_523_ = lean_st_ref_get(v___y_521_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc_ref(v_env_524_);
lean_dec(v___x_523_);
v___x_525_ = 0;
lean_inc(v_constName_517_);
v___x_526_ = l_Lean_Environment_find_x3f(v_env_524_, v_constName_517_, v___x_525_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v___x_527_;
}
else
{
lean_object* v_val_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_constName_517_);
v_val_528_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_526_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_val_528_);
lean_dec(v___x_526_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 0);
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_val_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0___boxed(lean_object* v_constName_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_constName_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(lean_object* v_x_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
switch(lean_obj_tag(v_x_543_))
{
case 0:
{
lean_object* v_declName_549_; lean_object* v___x_550_; 
v_declName_549_ = lean_ctor_get(v_x_543_, 0);
lean_inc_n(v_declName_549_, 2);
lean_dec_ref_known(v_x_543_, 1);
v___x_550_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_549_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_563_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_563_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_563_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_563_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_555_ = l_Lean_ConstantInfo_levelParams(v_a_551_);
lean_dec(v_a_551_);
v___x_556_ = lean_box(0);
lean_inc(v___x_555_);
v___x_557_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_555_, v___x_556_);
v___x_558_ = l_Lean_mkConst(v_declName_549_, v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_555_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_559_);
v___x_561_ = v___x_553_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v_declName_549_);
v_a_564_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_550_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_550_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_582_; 
v_fvarId_572_ = lean_ctor_get(v_x_543_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v_x_543_);
if (v_isSharedCheck_582_ == 0)
{
v___x_574_ = v_x_543_;
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_fvarId_572_);
lean_dec(v_x_543_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_576_ = lean_box(0);
v___x_577_ = l_Lean_mkFVar(v_fvarId_572_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 0);
lean_ctor_set(v___x_574_, 0, v___x_578_);
v___x_580_ = v___x_574_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
default: 
{
lean_object* v_proof_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_proof_583_ = lean_ctor_get(v_x_543_, 2);
lean_inc_ref(v_proof_583_);
lean_dec_ref_known(v_x_543_, 3);
v___x_584_ = lean_box(0);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v_proof_583_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof___boxed(lean_object* v_x_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(v_x_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0(lean_object* v_00_u03b1_594_, lean_object* v_constName_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___boxed(lean_object* v_00_u03b1_602_, lean_object* v_constName_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0(v_00_u03b1_602_, v_constName_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_610_, lean_object* v_ref_611_, lean_object* v_constName_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_611_, v_constName_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_619_, lean_object* v_ref_620_, lean_object* v_constName_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1(v_00_u03b1_619_, v_ref_620_, v_constName_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v_ref_620_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_628_, lean_object* v_ref_629_, lean_object* v_msg_630_, lean_object* v_declHint_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_629_, v_msg_630_, v_declHint_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_638_, lean_object* v_ref_639_, lean_object* v_msg_640_, lean_object* v_declHint_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_638_, v_ref_639_, v_msg_640_, v_declHint_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v_ref_639_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_648_, lean_object* v_declHint_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_648_, v_declHint_649_, v___y_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_656_, lean_object* v_declHint_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_656_, v_declHint_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_664_, lean_object* v_ref_665_, lean_object* v_msg_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_665_, v_msg_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_673_, lean_object* v_ref_674_, lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_673_, v_ref_674_, v_msg_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v_ref_674_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_682_, lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_690_, lean_object* v_msg_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(v_00_u03b1_690_, v_msg_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
return v_res_697_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0(void){
_start:
{
lean_object* v___x_698_; uint64_t v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(1723u);
v___x_699_ = lean_uint64_of_nat(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT uint64_t l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0(lean_object* v_sp_700_){
_start:
{
lean_object* v___y_702_; lean_object* v_declName_705_; 
v_declName_705_ = lean_ctor_get(v_sp_700_, 0);
v___y_702_ = v_declName_705_;
goto v___jp_701_;
v___jp_701_:
{
if (lean_obj_tag(v___y_702_) == 0)
{
uint64_t v___x_703_; 
v___x_703_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
return v___x_703_;
}
else
{
uint64_t v_hash_704_; 
v_hash_704_ = lean_ctor_get_uint64(v___y_702_, sizeof(void*)*2);
return v_hash_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___boxed(lean_object* v_sp_706_){
_start:
{
uint64_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0(v_sp_706_);
lean_dec_ref(v_sp_706_);
v_r_708_ = lean_box_uint64(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(lean_object* v_e_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_714_; 
v___x_714_ = l_Lean_Expr_hasMVar(v_e_711_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_e_711_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; lean_object* v_mctx_717_; lean_object* v___x_718_; lean_object* v_fst_719_; lean_object* v_snd_720_; lean_object* v___x_721_; lean_object* v_cache_722_; lean_object* v_zetaDeltaFVarIds_723_; lean_object* v_postponed_724_; lean_object* v_diag_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_734_; 
v___x_716_ = lean_st_ref_get(v___y_712_);
v_mctx_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref(v_mctx_717_);
lean_dec(v___x_716_);
v___x_718_ = l_Lean_instantiateMVarsCore(v_mctx_717_, v_e_711_);
v_fst_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_fst_719_);
v_snd_720_ = lean_ctor_get(v___x_718_, 1);
lean_inc(v_snd_720_);
lean_dec_ref(v___x_718_);
v___x_721_ = lean_st_ref_take(v___y_712_);
v_cache_722_ = lean_ctor_get(v___x_721_, 1);
v_zetaDeltaFVarIds_723_ = lean_ctor_get(v___x_721_, 2);
v_postponed_724_ = lean_ctor_get(v___x_721_, 3);
v_diag_725_ = lean_ctor_get(v___x_721_, 4);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___x_721_, 0);
lean_dec(v_unused_735_);
v___x_727_ = v___x_721_;
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_diag_725_);
lean_inc(v_postponed_724_);
lean_inc(v_zetaDeltaFVarIds_723_);
lean_inc(v_cache_722_);
lean_dec(v___x_721_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v_snd_720_);
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_snd_720_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_cache_722_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_zetaDeltaFVarIds_723_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_postponed_724_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_diag_725_);
v___x_730_ = v_reuseFailAlloc_733_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_st_ref_set(v___y_712_, v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v_fst_719_);
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg___boxed(lean_object* v_e_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_e_736_, v___y_737_);
lean_dec(v___y_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0(lean_object* v_e_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_e_740_, v___y_742_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___boxed(lean_object* v_e_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0(v_e_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(lean_object* v_proof_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_prf_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; 
switch(lean_obj_tag(v_proof_754_))
{
case 0:
{
lean_object* v_declName_816_; lean_object* v___x_817_; 
v_declName_816_ = lean_ctor_get(v_proof_754_, 0);
lean_inc(v_declName_816_);
lean_dec_ref_known(v_proof_754_, 1);
v___x_817_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_816_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v_prf_761_ = v_a_818_;
v___y_762_ = v_a_755_;
v___y_763_ = v_a_756_;
v___y_764_ = v_a_757_;
v___y_765_ = v_a_758_;
goto v___jp_760_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
v_a_819_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_817_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_817_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_827_; lean_object* v___x_828_; 
v_fvarId_827_ = lean_ctor_get(v_proof_754_, 0);
lean_inc(v_fvarId_827_);
lean_dec_ref_known(v_proof_754_, 1);
v___x_828_ = l_Lean_mkFVar(v_fvarId_827_);
v_prf_761_ = v___x_828_;
v___y_762_ = v_a_755_;
v___y_763_ = v_a_756_;
v___y_764_ = v_a_757_;
v___y_765_ = v_a_758_;
goto v___jp_760_;
}
default: 
{
lean_object* v_proof_829_; 
v_proof_829_ = lean_ctor_get(v_proof_754_, 2);
lean_inc_ref(v_proof_829_);
lean_dec_ref_known(v_proof_754_, 3);
v_prf_761_ = v_proof_829_;
v___y_762_ = v_a_755_;
v___y_763_ = v_a_756_;
v___y_764_ = v_a_757_;
v___y_765_ = v_a_758_;
goto v___jp_760_;
}
}
v___jp_760_:
{
lean_object* v___x_766_; 
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc_ref(v_prf_761_);
v___x_766_ = lean_infer_type(v_prf_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v_a_769_; uint8_t v___x_770_; lean_object* v___x_771_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_a_767_, v___y_763_);
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
v___x_770_ = 0;
v___x_771_ = l_Lean_Meta_forallMetaTelescope(v_a_769_, v___x_770_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_799_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_799_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_799_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_799_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_snd_776_; lean_object* v_fst_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_798_; 
v_snd_776_ = lean_ctor_get(v_a_772_, 1);
v_fst_777_ = lean_ctor_get(v_a_772_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v_a_772_);
if (v_isSharedCheck_798_ == 0)
{
v___x_779_ = v_a_772_;
v_isShared_780_ = v_isSharedCheck_798_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_snd_776_);
lean_inc(v_fst_777_);
lean_dec(v_a_772_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_798_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_fst_781_; lean_object* v_snd_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_797_; 
v_fst_781_ = lean_ctor_get(v_snd_776_, 0);
v_snd_782_ = lean_ctor_get(v_snd_776_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_snd_776_);
if (v_isSharedCheck_797_ == 0)
{
v___x_784_ = v_snd_776_;
v_isShared_785_ = v_isSharedCheck_797_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_snd_782_);
lean_inc(v_fst_781_);
lean_dec(v_snd_776_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_797_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
lean_inc(v_fst_777_);
v___x_786_ = l_Lean_Expr_beta(v_prf_761_, v_fst_777_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_snd_782_);
v___x_788_ = v_reuseFailAlloc_796_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_788_);
lean_ctor_set(v___x_779_, 0, v_fst_781_);
v___x_790_ = v___x_779_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_fst_781_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_788_);
v___x_790_ = v_reuseFailAlloc_795_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_fst_777_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_791_);
v___x_793_ = v___x_774_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v_prf_761_);
v_a_800_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_771_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_771_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_prf_761_);
v_a_808_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_766_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_766_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate___boxed(lean_object* v_proof_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(v_proof_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
return v_res_836_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0));
v___x_839_ = l_Lean_stringToMessageData(v___x_838_);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2));
v___x_842_ = l_Lean_stringToMessageData(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4));
v___x_845_ = l_Lean_stringToMessageData(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6));
v___x_848_ = l_Lean_stringToMessageData(v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0(lean_object* v_x_849_){
_start:
{
switch(lean_obj_tag(v_x_849_))
{
case 0:
{
lean_object* v_declName_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_declName_850_ = lean_ctor_get(v_x_849_, 0);
lean_inc(v_declName_850_);
lean_dec_ref_known(v_x_849_, 1);
v___x_851_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1);
v___x_852_ = l_Lean_MessageData_ofName(v_declName_850_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
return v___x_853_;
}
case 1:
{
lean_object* v_fvarId_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_fvarId_854_ = lean_ctor_get(v_x_849_, 0);
lean_inc(v_fvarId_854_);
lean_dec_ref_known(v_x_849_, 1);
v___x_855_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3);
v___x_856_ = l_Lean_mkFVar(v_fvarId_854_);
v___x_857_ = l_Lean_MessageData_ofExpr(v___x_856_);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_855_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
return v___x_858_;
}
default: 
{
lean_object* v_ref_859_; lean_object* v_proof_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_ref_859_ = lean_ctor_get(v_x_849_, 1);
lean_inc(v_ref_859_);
v_proof_860_ = lean_ctor_get(v_x_849_, 2);
lean_inc_ref(v_proof_860_);
lean_dec_ref_known(v_x_849_, 3);
v___x_861_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5);
v___x_862_ = l_Lean_MessageData_ofSyntax(v_ref_859_);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l_Lean_MessageData_ofExpr(v_proof_860_);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
return v___x_867_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = lean_box(0);
v___x_876_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2));
v___x_877_ = l_Lean_Expr_const___override(v___x_876_, v___x_875_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_878_ = lean_unsigned_to_nat(1000u);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default));
v___x_881_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3);
v___x_882_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0));
v___x_883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___x_881_);
lean_ctor_set(v___x_883_, 2, v___x_880_);
lean_ctor_set(v___x_883_, 3, v___x_879_);
lean_ctor_set(v___x_883_, 4, v___x_878_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default(void){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4);
return v___x_884_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem(void){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default;
return v___x_885_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(lean_object* v_xs_886_, lean_object* v_ys_887_, lean_object* v_x_888_){
_start:
{
lean_object* v_zero_889_; uint8_t v_isZero_890_; 
v_zero_889_ = lean_unsigned_to_nat(0u);
v_isZero_890_ = lean_nat_dec_eq(v_x_888_, v_zero_889_);
if (v_isZero_890_ == 1)
{
lean_dec(v_x_888_);
return v_isZero_890_;
}
else
{
lean_object* v_one_891_; lean_object* v_n_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_one_891_ = lean_unsigned_to_nat(1u);
v_n_892_ = lean_nat_sub(v_x_888_, v_one_891_);
lean_dec(v_x_888_);
v___x_893_ = lean_array_fget_borrowed(v_xs_886_, v_n_892_);
v___x_894_ = lean_array_fget_borrowed(v_ys_887_, v_n_892_);
v___x_895_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_dec(v_n_892_);
return v___x_895_;
}
else
{
v_x_888_ = v_n_892_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg___boxed(lean_object* v_xs_897_, lean_object* v_ys_898_, lean_object* v_x_899_){
_start:
{
uint8_t v_res_900_; lean_object* v_r_901_; 
v_res_900_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_xs_897_, v_ys_898_, v_x_899_);
lean_dec_ref(v_ys_898_);
lean_dec_ref(v_xs_897_);
v_r_901_ = lean_box(v_res_900_);
return v_r_901_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
lean_object* v_keys_904_; lean_object* v_prog_905_; lean_object* v_proof_906_; lean_object* v_etaPotential_907_; lean_object* v_priority_908_; lean_object* v_keys_909_; lean_object* v_prog_910_; lean_object* v_proof_911_; lean_object* v_etaPotential_912_; lean_object* v_priority_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_keys_904_ = lean_ctor_get(v_x_902_, 0);
lean_inc_ref(v_keys_904_);
v_prog_905_ = lean_ctor_get(v_x_902_, 1);
lean_inc_ref(v_prog_905_);
v_proof_906_ = lean_ctor_get(v_x_902_, 2);
lean_inc_ref(v_proof_906_);
v_etaPotential_907_ = lean_ctor_get(v_x_902_, 3);
lean_inc(v_etaPotential_907_);
v_priority_908_ = lean_ctor_get(v_x_902_, 4);
lean_inc(v_priority_908_);
lean_dec_ref(v_x_902_);
v_keys_909_ = lean_ctor_get(v_x_903_, 0);
lean_inc_ref(v_keys_909_);
v_prog_910_ = lean_ctor_get(v_x_903_, 1);
lean_inc_ref(v_prog_910_);
v_proof_911_ = lean_ctor_get(v_x_903_, 2);
lean_inc_ref(v_proof_911_);
v_etaPotential_912_ = lean_ctor_get(v_x_903_, 3);
lean_inc(v_etaPotential_912_);
v_priority_913_ = lean_ctor_get(v_x_903_, 4);
lean_inc(v_priority_913_);
lean_dec_ref(v_x_903_);
v___x_914_ = lean_array_get_size(v_keys_904_);
v___x_915_ = lean_array_get_size(v_keys_909_);
v___x_916_ = lean_nat_dec_eq(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_dec(v_priority_913_);
lean_dec(v_etaPotential_912_);
lean_dec_ref(v_proof_911_);
lean_dec_ref(v_prog_910_);
lean_dec_ref(v_keys_909_);
lean_dec(v_priority_908_);
lean_dec(v_etaPotential_907_);
lean_dec_ref(v_proof_906_);
lean_dec_ref(v_prog_905_);
lean_dec_ref(v_keys_904_);
return v___x_916_;
}
else
{
uint8_t v___x_917_; 
v___x_917_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_keys_904_, v_keys_909_, v___x_914_);
lean_dec_ref(v_keys_909_);
lean_dec_ref(v_keys_904_);
if (v___x_917_ == 0)
{
lean_dec(v_priority_913_);
lean_dec(v_etaPotential_912_);
lean_dec_ref(v_proof_911_);
lean_dec_ref(v_prog_910_);
lean_dec(v_priority_908_);
lean_dec(v_etaPotential_907_);
lean_dec_ref(v_proof_906_);
lean_dec_ref(v_prog_905_);
return v___x_917_;
}
else
{
uint8_t v___x_918_; 
v___x_918_ = lean_expr_eqv(v_prog_905_, v_prog_910_);
lean_dec_ref(v_prog_910_);
lean_dec_ref(v_prog_905_);
if (v___x_918_ == 0)
{
lean_dec(v_priority_913_);
lean_dec(v_etaPotential_912_);
lean_dec_ref(v_proof_911_);
lean_dec(v_priority_908_);
lean_dec(v_etaPotential_907_);
lean_dec_ref(v_proof_906_);
return v___x_918_;
}
else
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_proof_906_, v_proof_911_);
if (v___x_919_ == 0)
{
lean_dec(v_priority_913_);
lean_dec(v_etaPotential_912_);
lean_dec(v_priority_908_);
lean_dec(v_etaPotential_907_);
return v___x_919_;
}
else
{
uint8_t v___x_920_; 
v___x_920_ = lean_nat_dec_eq(v_etaPotential_907_, v_etaPotential_912_);
lean_dec(v_etaPotential_912_);
lean_dec(v_etaPotential_907_);
if (v___x_920_ == 0)
{
lean_dec(v_priority_913_);
lean_dec(v_priority_908_);
return v___x_920_;
}
else
{
uint8_t v___x_921_; 
v___x_921_ = lean_nat_dec_eq(v_priority_908_, v_priority_913_);
lean_dec(v_priority_913_);
lean_dec(v_priority_908_);
return v___x_921_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq___boxed(lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
uint8_t v_res_924_; lean_object* v_r_925_; 
v_res_924_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(v_x_922_, v_x_923_);
v_r_925_ = lean_box(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(lean_object* v_xs_926_, lean_object* v_ys_927_, lean_object* v_hsz_928_, lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_xs_926_, v_ys_927_, v_x_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___boxed(lean_object* v_xs_932_, lean_object* v_ys_933_, lean_object* v_hsz_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
uint8_t v_res_937_; lean_object* v_r_938_; 
v_res_937_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(v_xs_932_, v_ys_933_, v_hsz_934_, v_x_935_, v_x_936_);
lean_dec_ref(v_ys_933_);
lean_dec_ref(v_xs_932_);
v_r_938_ = lean_box(v_res_937_);
return v_r_938_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_941_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(lean_object* v_00_u03b2_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(lean_box(0));
return v___x_947_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1);
v___x_949_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_948_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default(void){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems(void){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
return v___x_952_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(lean_object* v_msg_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0);
v___x_956_ = lean_panic_fn_borrowed(v___x_955_, v_msg_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4_spec__8(lean_object* v_xs_957_, lean_object* v_v_958_, lean_object* v_i_959_){
_start:
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = lean_array_get_size(v_xs_957_);
v___x_961_ = lean_nat_dec_lt(v_i_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec(v_i_959_);
v___x_962_ = lean_box(0);
return v___x_962_;
}
else
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_array_fget_borrowed(v_xs_957_, v_i_959_);
v___x_964_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_963_, v_v_958_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_add(v_i_959_, v___x_965_);
lean_dec(v_i_959_);
v_i_959_ = v___x_966_;
goto _start;
}
else
{
lean_object* v___x_968_; 
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v_i_959_);
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4_spec__8___boxed(lean_object* v_xs_969_, lean_object* v_v_970_, lean_object* v_i_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4_spec__8(v_xs_969_, v_v_970_, v_i_971_);
lean_dec(v_v_970_);
lean_dec_ref(v_xs_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4(lean_object* v_xs_973_, lean_object* v_v_974_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4_spec__8(v_xs_973_, v_v_974_, v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4___boxed(lean_object* v_xs_977_, lean_object* v_v_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4(v_xs_977_, v_v_978_);
lean_dec(v_v_978_);
lean_dec_ref(v_xs_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10_spec__11___redArg(lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
lean_object* v_ks_984_; lean_object* v_vs_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1009_; 
v_ks_984_ = lean_ctor_get(v_x_980_, 0);
v_vs_985_ = lean_ctor_get(v_x_980_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_987_ = v_x_980_;
v_isShared_988_ = v_isSharedCheck_1009_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_vs_985_);
lean_inc(v_ks_984_);
lean_dec(v_x_980_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1009_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = lean_array_get_size(v_ks_984_);
v___x_990_ = lean_nat_dec_lt(v_x_981_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
lean_dec(v_x_981_);
v___x_991_ = lean_array_push(v_ks_984_, v_x_982_);
v___x_992_ = lean_array_push(v_vs_985_, v_x_983_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v___x_992_);
lean_ctor_set(v___x_987_, 0, v___x_991_);
v___x_994_ = v___x_987_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
else
{
lean_object* v_k_x27_996_; uint8_t v___x_997_; 
v_k_x27_996_ = lean_array_fget_borrowed(v_ks_984_, v_x_981_);
v___x_997_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_982_, v_k_x27_996_);
if (v___x_997_ == 0)
{
lean_object* v___x_999_; 
if (v_isShared_988_ == 0)
{
v___x_999_ = v___x_987_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_ks_984_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_vs_985_);
v___x_999_ = v_reuseFailAlloc_1003_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = lean_nat_add(v_x_981_, v___x_1000_);
lean_dec(v_x_981_);
v_x_980_ = v___x_999_;
v_x_981_ = v___x_1001_;
goto _start;
}
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1004_ = lean_array_fset(v_ks_984_, v_x_981_, v_x_982_);
v___x_1005_ = lean_array_fset(v_vs_985_, v_x_981_, v_x_983_);
lean_dec(v_x_981_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v___x_1005_);
lean_ctor_set(v___x_987_, 0, v___x_1004_);
v___x_1007_ = v___x_987_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10___redArg(lean_object* v_n_1010_, lean_object* v_k_1011_, lean_object* v_v_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10_spec__11___redArg(v_n_1010_, v___x_1013_, v_k_1011_, v_v_1012_);
return v___x_1014_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; 
v___x_1015_ = ((size_t)5ULL);
v___x_1016_ = ((size_t)1ULL);
v___x_1017_ = lean_usize_shift_left(v___x_1016_, v___x_1015_);
return v___x_1017_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; 
v___x_1018_ = ((size_t)1ULL);
v___x_1019_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__0);
v___x_1020_ = lean_usize_sub(v___x_1019_, v___x_1018_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg(lean_object* v_x_1022_, size_t v_x_1023_, size_t v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
if (lean_obj_tag(v_x_1022_) == 0)
{
lean_object* v_es_1027_; size_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; size_t v___x_1031_; lean_object* v_j_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_es_1027_ = lean_ctor_get(v_x_1022_, 0);
v___x_1028_ = ((size_t)5ULL);
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1);
v___x_1031_ = lean_usize_land(v_x_1023_, v___x_1030_);
v_j_1032_ = lean_usize_to_nat(v___x_1031_);
v___x_1033_ = lean_array_get_size(v_es_1027_);
v___x_1034_ = lean_nat_dec_lt(v_j_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec(v_j_1032_);
lean_dec(v_x_1026_);
lean_dec(v_x_1025_);
return v_x_1022_;
}
else
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1071_; 
lean_inc_ref(v_es_1027_);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_x_1022_, 0);
lean_dec(v_unused_1072_);
v___x_1036_ = v_x_1022_;
v_isShared_1037_ = v_isSharedCheck_1071_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v_x_1022_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1071_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v_v_1038_; lean_object* v___x_1039_; lean_object* v_xs_x27_1040_; lean_object* v___y_1042_; 
v_v_1038_ = lean_array_fget(v_es_1027_, v_j_1032_);
v___x_1039_ = lean_box(0);
v_xs_x27_1040_ = lean_array_fset(v_es_1027_, v_j_1032_, v___x_1039_);
switch(lean_obj_tag(v_v_1038_))
{
case 0:
{
lean_object* v_key_1047_; lean_object* v_val_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1058_; 
v_key_1047_ = lean_ctor_get(v_v_1038_, 0);
v_val_1048_ = lean_ctor_get(v_v_1038_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_v_1038_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1050_ = v_v_1038_;
v_isShared_1051_ = v_isSharedCheck_1058_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_val_1048_);
lean_inc(v_key_1047_);
lean_dec(v_v_1038_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1058_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
uint8_t v___x_1052_; 
v___x_1052_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1025_, v_key_1047_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_del_object(v___x_1050_);
v___x_1053_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1047_, v_val_1048_, v_x_1025_, v_x_1026_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
v___y_1042_ = v___x_1054_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1056_; 
lean_dec(v_val_1048_);
lean_dec(v_key_1047_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v_x_1026_);
lean_ctor_set(v___x_1050_, 0, v_x_1025_);
v___x_1056_ = v___x_1050_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_x_1025_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_x_1026_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
v___y_1042_ = v___x_1056_;
goto v___jp_1041_;
}
}
}
}
case 1:
{
lean_object* v_node_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1069_; 
v_node_1059_ = lean_ctor_get(v_v_1038_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_v_1038_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1061_ = v_v_1038_;
v_isShared_1062_ = v_isSharedCheck_1069_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_node_1059_);
lean_dec(v_v_1038_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1069_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1063_ = lean_usize_shift_right(v_x_1023_, v___x_1028_);
v___x_1064_ = lean_usize_add(v_x_1024_, v___x_1029_);
v___x_1065_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg(v_node_1059_, v___x_1063_, v___x_1064_, v_x_1025_, v_x_1026_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1065_);
v___x_1067_ = v___x_1061_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
v___y_1042_ = v___x_1067_;
goto v___jp_1041_;
}
}
}
default: 
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_x_1025_);
lean_ctor_set(v___x_1070_, 1, v_x_1026_);
v___y_1042_ = v___x_1070_;
goto v___jp_1041_;
}
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = lean_array_fset(v_xs_x27_1040_, v_j_1032_, v___y_1042_);
lean_dec(v_j_1032_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1043_);
v___x_1045_ = v___x_1036_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
else
{
lean_object* v_ks_1073_; lean_object* v_vs_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1094_; 
v_ks_1073_ = lean_ctor_get(v_x_1022_, 0);
v_vs_1074_ = lean_ctor_get(v_x_1022_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1076_ = v_x_1022_;
v_isShared_1077_ = v_isSharedCheck_1094_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_vs_1074_);
lean_inc(v_ks_1073_);
lean_dec(v_x_1022_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1094_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_ks_1073_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_vs_1074_);
v___x_1079_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v_newNode_1080_; uint8_t v___y_1082_; size_t v___x_1088_; uint8_t v___x_1089_; 
v_newNode_1080_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10___redArg(v___x_1079_, v_x_1025_, v_x_1026_);
v___x_1088_ = ((size_t)7ULL);
v___x_1089_ = lean_usize_dec_le(v___x_1088_, v_x_1024_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1090_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1080_);
v___x_1091_ = lean_unsigned_to_nat(4u);
v___x_1092_ = lean_nat_dec_lt(v___x_1090_, v___x_1091_);
lean_dec(v___x_1090_);
v___y_1082_ = v___x_1092_;
goto v___jp_1081_;
}
else
{
v___y_1082_ = v___x_1089_;
goto v___jp_1081_;
}
v___jp_1081_:
{
if (v___y_1082_ == 0)
{
lean_object* v_ks_1083_; lean_object* v_vs_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_ks_1083_ = lean_ctor_get(v_newNode_1080_, 0);
lean_inc_ref(v_ks_1083_);
v_vs_1084_ = lean_ctor_get(v_newNode_1080_, 1);
lean_inc_ref(v_vs_1084_);
lean_dec_ref(v_newNode_1080_);
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__2);
v___x_1087_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11___redArg(v_x_1024_, v_ks_1083_, v_vs_1084_, v___x_1085_, v___x_1086_);
lean_dec_ref(v_vs_1084_);
lean_dec_ref(v_ks_1083_);
return v___x_1087_;
}
else
{
return v_newNode_1080_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11___redArg(size_t v_depth_1095_, lean_object* v_keys_1096_, lean_object* v_vals_1097_, lean_object* v_i_1098_, lean_object* v_entries_1099_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_array_get_size(v_keys_1096_);
v___x_1101_ = lean_nat_dec_lt(v_i_1098_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec(v_i_1098_);
return v_entries_1099_;
}
else
{
lean_object* v_k_1102_; lean_object* v_v_1103_; uint64_t v___x_1104_; size_t v_h_1105_; size_t v___x_1106_; lean_object* v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; size_t v_h_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_k_1102_ = lean_array_fget_borrowed(v_keys_1096_, v_i_1098_);
v_v_1103_ = lean_array_fget_borrowed(v_vals_1097_, v_i_1098_);
v___x_1104_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1102_);
v_h_1105_ = lean_uint64_to_usize(v___x_1104_);
v___x_1106_ = ((size_t)5ULL);
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_sub(v_depth_1095_, v___x_1108_);
v___x_1110_ = lean_usize_mul(v___x_1106_, v___x_1109_);
v_h_1111_ = lean_usize_shift_right(v_h_1105_, v___x_1110_);
v___x_1112_ = lean_nat_add(v_i_1098_, v___x_1107_);
lean_dec(v_i_1098_);
lean_inc(v_v_1103_);
lean_inc(v_k_1102_);
v___x_1113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg(v_entries_1099_, v_h_1111_, v_depth_1095_, v_k_1102_, v_v_1103_);
v_i_1098_ = v___x_1112_;
v_entries_1099_ = v___x_1113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_depth_1115_, lean_object* v_keys_1116_, lean_object* v_vals_1117_, lean_object* v_i_1118_, lean_object* v_entries_1119_){
_start:
{
size_t v_depth_boxed_1120_; lean_object* v_res_1121_; 
v_depth_boxed_1120_ = lean_unbox_usize(v_depth_1115_);
lean_dec(v_depth_1115_);
v_res_1121_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11___redArg(v_depth_boxed_1120_, v_keys_1116_, v_vals_1117_, v_i_1118_, v_entries_1119_);
lean_dec_ref(v_vals_1117_);
lean_dec_ref(v_keys_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
size_t v_x_1679__boxed_1127_; size_t v_x_1680__boxed_1128_; lean_object* v_res_1129_; 
v_x_1679__boxed_1127_ = lean_unbox_usize(v_x_1123_);
lean_dec(v_x_1123_);
v_x_1680__boxed_1128_ = lean_unbox_usize(v_x_1124_);
lean_dec(v_x_1124_);
v_res_1129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg(v_x_1122_, v_x_1679__boxed_1127_, v_x_1680__boxed_1128_, v_x_1125_, v_x_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_vs_1130_, lean_object* v_v_1131_, lean_object* v_i_1132_){
_start:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_array_get_size(v_vs_1130_);
v___x_1134_ = lean_nat_dec_lt(v_i_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec(v_i_1132_);
v___x_1135_ = lean_array_push(v_vs_1130_, v_v_1131_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = lean_array_fget_borrowed(v_vs_1130_, v_i_1132_);
lean_inc(v___x_1136_);
lean_inc_ref(v_v_1131_);
v___x_1137_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(v_v_1131_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = lean_nat_add(v_i_1132_, v___x_1138_);
lean_dec(v_i_1132_);
v_i_1132_ = v___x_1139_;
goto _start;
}
else
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_array_fset(v_vs_1130_, v_i_1132_, v_v_1131_);
lean_dec(v_i_1132_);
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(lean_object* v_vs_1142_, lean_object* v_v_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(v_vs_1142_, v_v_1143_, v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(lean_object* v_x_1146_, lean_object* v_keys_1147_, lean_object* v_v_1148_, lean_object* v_k_1149_, lean_object* v_x_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_c_1153_; lean_object* v___x_1154_; 
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_add(v_x_1146_, v___x_1151_);
v_c_1153_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1147_, v_v_1148_, v___x_1152_);
lean_dec(v___x_1152_);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v_k_1149_);
lean_ctor_set(v___x_1154_, 1, v_c_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_x_1155_, lean_object* v_keys_1156_, lean_object* v_v_1157_, lean_object* v_k_1158_, lean_object* v_x_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(v_x_1155_, v_keys_1156_, v_v_1157_, v_k_1158_, v_x_1159_);
lean_dec_ref(v_keys_1156_);
lean_dec(v_x_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1(lean_object* v_a_1161_, lean_object* v_b_1162_){
_start:
{
lean_object* v_fst_1163_; lean_object* v_fst_1164_; uint8_t v___x_1165_; 
v_fst_1163_ = lean_ctor_get(v_a_1161_, 0);
v_fst_1164_ = lean_ctor_get(v_b_1162_, 0);
v___x_1165_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1163_, v_fst_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* v_a_1166_, lean_object* v_b_1167_){
_start:
{
uint8_t v_res_1168_; lean_object* v_r_1169_; 
v_res_1168_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1(v_a_1166_, v_b_1167_);
lean_dec_ref(v_b_1167_);
lean_dec_ref(v_a_1166_);
v_r_1169_ = lean_box(v_res_1168_);
return v_r_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_1174_, lean_object* v_keys_1175_, lean_object* v_v_1176_, lean_object* v_k_1177_, lean_object* v_as_1178_, lean_object* v_k_1179_, lean_object* v_x_1180_, lean_object* v_x_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_mid_1184_; lean_object* v_midVal_1185_; uint8_t v___x_1186_; 
v___x_1182_ = lean_nat_add(v_x_1180_, v_x_1181_);
v___x_1183_ = lean_unsigned_to_nat(1u);
v_mid_1184_ = lean_nat_shiftr(v___x_1182_, v___x_1183_);
lean_dec(v___x_1182_);
v_midVal_1185_ = lean_array_fget(v_as_1178_, v_mid_1184_);
v___x_1186_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1(v_midVal_1185_, v_k_1179_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; 
lean_dec(v_x_1181_);
v___x_1187_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1(v_k_1179_, v_midVal_1185_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
lean_dec(v_x_1180_);
v___x_1188_ = lean_array_get_size(v_as_1178_);
v___x_1189_ = lean_nat_dec_lt(v_mid_1184_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_dec(v_midVal_1185_);
lean_dec(v_mid_1184_);
lean_dec(v_k_1177_);
lean_dec_ref(v_v_1176_);
return v_as_1178_;
}
else
{
lean_object* v_snd_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1202_; 
v_snd_1190_ = lean_ctor_get(v_midVal_1185_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_midVal_1185_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v_midVal_1185_, 0);
lean_dec(v_unused_1203_);
v___x_1192_ = v_midVal_1185_;
v_isShared_1193_ = v_isSharedCheck_1202_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snd_1190_);
lean_dec(v_midVal_1185_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1202_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v_xs_x27_1195_; lean_object* v___x_1196_; lean_object* v_c_1197_; lean_object* v___x_1199_; 
v___x_1194_ = lean_box(0);
v_xs_x27_1195_ = lean_array_fset(v_as_1178_, v_mid_1184_, v___x_1194_);
v___x_1196_ = lean_nat_add(v_x_1174_, v___x_1183_);
v_c_1197_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(v_keys_1175_, v_v_1176_, v___x_1196_, v_snd_1190_);
lean_dec(v___x_1196_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v_c_1197_);
lean_ctor_set(v___x_1192_, 0, v_k_1177_);
v___x_1199_ = v___x_1192_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_k_1177_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_c_1197_);
v___x_1199_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_array_fset(v_xs_x27_1195_, v_mid_1184_, v___x_1199_);
lean_dec(v_mid_1184_);
return v___x_1200_;
}
}
}
}
else
{
lean_dec(v_midVal_1185_);
v_x_1181_ = v_mid_1184_;
goto _start;
}
}
else
{
uint8_t v___x_1205_; 
lean_dec(v_midVal_1185_);
v___x_1205_ = lean_nat_dec_eq(v_mid_1184_, v_x_1180_);
if (v___x_1205_ == 0)
{
lean_dec(v_x_1180_);
v_x_1180_ = v_mid_1184_;
goto _start;
}
else
{
lean_object* v___x_1207_; lean_object* v_c_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_j_1211_; lean_object* v_as_1212_; lean_object* v___x_1213_; 
lean_dec(v_mid_1184_);
lean_dec(v_x_1181_);
v___x_1207_ = lean_nat_add(v_x_1174_, v___x_1183_);
v_c_1208_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1175_, v_v_1176_, v___x_1207_);
lean_dec(v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v_k_1177_);
lean_ctor_set(v___x_1209_, 1, v_c_1208_);
v___x_1210_ = lean_nat_add(v_x_1180_, v___x_1183_);
lean_dec(v_x_1180_);
v_j_1211_ = lean_array_get_size(v_as_1178_);
v_as_1212_ = lean_array_push(v_as_1178_, v___x_1209_);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1210_, v_as_1212_, v_j_1211_);
lean_dec(v___x_1210_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2(lean_object* v_x_1214_, lean_object* v_keys_1215_, lean_object* v_v_1216_, lean_object* v_k_1217_, lean_object* v_as_1218_, lean_object* v_k_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1220_ = lean_array_get_size(v_as_1218_);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_nat_dec_eq(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_array_fget_borrowed(v_as_1218_, v___x_1221_);
v___x_1224_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1(v_k_1219_, v___x_1223_);
if (v___x_1224_ == 0)
{
uint8_t v___x_1225_; 
v___x_1225_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1(v___x_1223_, v_k_1219_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; 
v___x_1226_ = lean_nat_dec_lt(v___x_1221_, v___x_1220_);
if (v___x_1226_ == 0)
{
lean_dec(v_k_1217_);
lean_dec_ref(v_v_1216_);
return v_as_1218_;
}
else
{
lean_object* v___x_1227_; lean_object* v_xs_x27_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_inc(v___x_1223_);
v___x_1227_ = lean_box(0);
v_xs_x27_1228_ = lean_array_fset(v_as_1218_, v___x_1221_, v___x_1227_);
v___x_1229_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__2(v_x_1214_, v_keys_1215_, v_v_1216_, v_k_1217_, v___x_1223_);
v___x_1230_ = lean_array_fset(v_xs_x27_1228_, v___x_1221_, v___x_1229_);
return v___x_1230_;
}
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_sub(v___x_1220_, v___x_1231_);
v___x_1233_ = lean_array_fget_borrowed(v_as_1218_, v___x_1232_);
v___x_1234_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1(v___x_1233_, v_k_1219_);
if (v___x_1234_ == 0)
{
uint8_t v___x_1235_; 
v___x_1235_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__1(v_k_1219_, v___x_1233_);
if (v___x_1235_ == 0)
{
uint8_t v___x_1236_; 
v___x_1236_ = lean_nat_dec_lt(v___x_1232_, v___x_1220_);
if (v___x_1236_ == 0)
{
lean_dec(v___x_1232_);
lean_dec(v_k_1217_);
lean_dec_ref(v_v_1216_);
return v_as_1218_;
}
else
{
lean_object* v___x_1237_; lean_object* v_xs_x27_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_inc(v___x_1233_);
v___x_1237_ = lean_box(0);
v_xs_x27_1238_ = lean_array_fset(v_as_1218_, v___x_1232_, v___x_1237_);
v___x_1239_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__2(v_x_1214_, v_keys_1215_, v_v_1216_, v_k_1217_, v___x_1233_);
v___x_1240_ = lean_array_fset(v_xs_x27_1238_, v___x_1232_, v___x_1239_);
lean_dec(v___x_1232_);
return v___x_1240_;
}
}
else
{
lean_object* v___x_1241_; 
v___x_1241_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1214_, v_keys_1215_, v_v_1216_, v_k_1217_, v_as_1218_, v_k_1219_, v___x_1221_, v___x_1232_);
return v___x_1241_;
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v___x_1232_);
v___x_1242_ = lean_box(0);
v___x_1243_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(v_x_1214_, v_keys_1215_, v_v_1216_, v_k_1217_, v___x_1242_);
v___x_1244_ = lean_array_push(v_as_1218_, v___x_1243_);
return v___x_1244_;
}
}
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v_as_1247_; lean_object* v___x_1248_; 
v___x_1245_ = lean_box(0);
v___x_1246_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(v_x_1214_, v_keys_1215_, v_v_1216_, v_k_1217_, v___x_1245_);
v_as_1247_ = lean_array_push(v_as_1218_, v___x_1246_);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1221_, v_as_1247_, v___x_1220_);
return v___x_1248_;
}
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(v_x_1214_, v_keys_1215_, v_v_1216_, v_k_1217_, v___x_1249_);
v___x_1251_ = lean_array_push(v_as_1218_, v___x_1250_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(lean_object* v_keys_1252_, lean_object* v_v_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v_vs_1256_; lean_object* v_children_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1274_; 
v_vs_1256_ = lean_ctor_get(v_x_1255_, 0);
v_children_1257_ = lean_ctor_get(v_x_1255_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_x_1255_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1259_ = v_x_1255_;
v_isShared_1260_ = v_isSharedCheck_1274_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_children_1257_);
lean_inc(v_vs_1256_);
lean_dec(v_x_1255_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1274_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = lean_array_get_size(v_keys_1252_);
v___x_1262_ = lean_nat_dec_lt(v_x_1254_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(v_vs_1256_, v_v_1253_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1263_);
v___x_1265_ = v___x_1259_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_children_1257_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
else
{
lean_object* v_k_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_c_1270_; lean_object* v___x_1272_; 
v_k_1267_ = lean_array_fget_borrowed(v_keys_1252_, v_x_1254_);
v___x_1268_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___closed__1));
lean_inc_n(v_k_1267_, 2);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_k_1267_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v_c_1270_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2(v_x_1254_, v_keys_1252_, v_v_1253_, v_k_1267_, v_children_1257_, v___x_1269_);
lean_dec_ref_known(v___x_1269_, 2);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_c_1270_);
v___x_1272_ = v___x_1259_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_vs_1256_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_c_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__2(lean_object* v_x_1275_, lean_object* v_keys_1276_, lean_object* v_v_1277_, lean_object* v_k_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v_snd_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1290_; 
v_snd_1280_ = lean_ctor_get(v_x_1279_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_x_1279_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v_x_1279_, 0);
lean_dec(v_unused_1291_);
v___x_1282_ = v_x_1279_;
v_isShared_1283_ = v_isSharedCheck_1290_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_snd_1280_);
lean_dec(v_x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1290_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_c_1286_; lean_object* v___x_1288_; 
v___x_1284_ = lean_unsigned_to_nat(1u);
v___x_1285_ = lean_nat_add(v_x_1275_, v___x_1284_);
v_c_1286_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(v_keys_1276_, v_v_1277_, v___x_1285_, v_snd_1280_);
lean_dec(v___x_1285_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v_c_1286_);
lean_ctor_set(v___x_1282_, 0, v_k_1278_);
v___x_1288_ = v___x_1282_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_k_1278_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_c_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_1292_, lean_object* v_keys_1293_, lean_object* v_v_1294_, lean_object* v_k_1295_, lean_object* v_x_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__2(v_x_1292_, v_keys_1293_, v_v_1294_, v_k_1295_, v_x_1296_);
lean_dec_ref(v_keys_1293_);
lean_dec(v_x_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___boxed(lean_object* v_keys_1298_, lean_object* v_v_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(v_keys_1298_, v_v_1299_, v_x_1300_, v_x_1301_);
lean_dec(v_x_1300_);
lean_dec_ref(v_keys_1298_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_x_1303_, lean_object* v_keys_1304_, lean_object* v_v_1305_, lean_object* v_k_1306_, lean_object* v_as_1307_, lean_object* v_k_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1303_, v_keys_1304_, v_v_1305_, v_k_1306_, v_as_1307_, v_k_1308_, v_x_1309_, v_x_1310_);
lean_dec_ref(v_k_1308_);
lean_dec_ref(v_keys_1304_);
lean_dec(v_x_1303_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_x_1312_, lean_object* v_keys_1313_, lean_object* v_v_1314_, lean_object* v_k_1315_, lean_object* v_as_1316_, lean_object* v_k_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2(v_x_1312_, v_keys_1313_, v_v_1314_, v_k_1315_, v_as_1316_, v_k_1317_);
lean_dec_ref(v_k_1317_);
lean_dec_ref(v_keys_1313_);
lean_dec(v_x_1312_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___lam__0(lean_object* v_keys_1319_, lean_object* v_v_1320_, lean_object* v_x_1321_){
_start:
{
if (lean_obj_tag(v_x_1321_) == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1319_, v_v_1320_, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
else
{
lean_object* v_val_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1334_; 
v_val_1325_ = lean_ctor_get(v_x_1321_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_x_1321_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1327_ = v_x_1321_;
v_isShared_1328_ = v_isSharedCheck_1334_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_val_1325_);
lean_dec(v_x_1321_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1334_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(v_keys_1319_, v_v_1320_, v___x_1329_, v_val_1325_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1330_);
v___x_1332_ = v___x_1327_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___lam__0___boxed(lean_object* v_keys_1335_, lean_object* v_v_1336_, lean_object* v_x_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___lam__0(v_keys_1335_, v_v_1336_, v_x_1337_);
lean_dec_ref(v_keys_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1(lean_object* v_keys_1339_, lean_object* v_v_1340_, lean_object* v_x_1341_, size_t v_x_1342_, size_t v_x_1343_, lean_object* v_x_1344_){
_start:
{
if (lean_obj_tag(v_x_1341_) == 0)
{
lean_object* v_es_1345_; size_t v___x_1346_; size_t v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; lean_object* v_j_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_es_1345_ = lean_ctor_get(v_x_1341_, 0);
v___x_1346_ = ((size_t)5ULL);
v___x_1347_ = ((size_t)1ULL);
v___x_1348_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1);
v___x_1349_ = lean_usize_land(v_x_1342_, v___x_1348_);
v_j_1350_ = lean_usize_to_nat(v___x_1349_);
v___x_1351_ = lean_array_get_size(v_es_1345_);
v___x_1352_ = lean_nat_dec_lt(v_j_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec(v_j_1350_);
lean_dec(v_x_1344_);
lean_dec_ref(v_v_1340_);
return v_x_1341_;
}
else
{
lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1418_; 
lean_inc_ref(v_es_1345_);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1341_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; 
v_unused_1419_ = lean_ctor_get(v_x_1341_, 0);
lean_dec(v_unused_1419_);
v___x_1354_ = v_x_1341_;
v_isShared_1355_ = v_isSharedCheck_1418_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v_x_1341_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1418_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_v_1356_; lean_object* v___x_1357_; lean_object* v_xs_x27_1358_; lean_object* v___y_1360_; 
v_v_1356_ = lean_array_fget(v_es_1345_, v_j_1350_);
v___x_1357_ = lean_box(0);
v_xs_x27_1358_ = lean_array_fset(v_es_1345_, v_j_1350_, v___x_1357_);
switch(lean_obj_tag(v_v_1356_))
{
case 0:
{
lean_object* v_key_1365_; lean_object* v_val_1366_; uint8_t v___x_1367_; 
v_key_1365_ = lean_ctor_get(v_v_1356_, 0);
v_val_1366_ = lean_ctor_get(v_v_1356_, 1);
v___x_1367_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1344_, v_key_1365_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___lam__0(v_keys_1339_, v_v_1340_, v___x_1368_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_dec(v_x_1344_);
v___y_1360_ = v_v_1356_;
goto v___jp_1359_;
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1378_; 
lean_inc(v_val_1366_);
lean_inc(v_key_1365_);
lean_dec_ref_known(v_v_1356_, 2);
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_val_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1365_, v_val_1366_, v_x_1344_, v_val_1370_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1374_);
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
v___y_1360_ = v___x_1376_;
goto v___jp_1359_;
}
}
}
}
else
{
lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1389_; 
lean_inc(v_val_1366_);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_v_1356_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; lean_object* v_unused_1391_; 
v_unused_1390_ = lean_ctor_get(v_v_1356_, 1);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v_v_1356_, 0);
lean_dec(v_unused_1391_);
v___x_1380_ = v_v_1356_;
v_isShared_1381_ = v_isSharedCheck_1389_;
goto v_resetjp_1379_;
}
else
{
lean_dec(v_v_1356_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1389_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_val_1366_);
v___x_1383_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___lam__0(v_keys_1339_, v_v_1340_, v___x_1382_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; 
lean_del_object(v___x_1380_);
lean_dec(v_x_1344_);
v___x_1384_ = lean_box(2);
v___y_1360_ = v___x_1384_;
goto v___jp_1359_;
}
else
{
lean_object* v_val_1385_; lean_object* v___x_1387_; 
v_val_1385_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v___x_1383_, 1);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v_val_1385_);
lean_ctor_set(v___x_1380_, 0, v_x_1344_);
v___x_1387_ = v___x_1380_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_x_1344_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_val_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
v___y_1360_ = v___x_1387_;
goto v___jp_1359_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1413_; 
v_node_1392_ = lean_ctor_get(v_v_1356_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_v_1356_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1394_ = v_v_1356_;
v_isShared_1395_ = v_isSharedCheck_1413_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_node_1392_);
lean_dec(v_v_1356_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1413_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
size_t v___x_1396_; size_t v___x_1397_; lean_object* v_newNode_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_usize_shift_right(v_x_1342_, v___x_1346_);
v___x_1397_ = lean_usize_add(v_x_1343_, v___x_1347_);
v_newNode_1398_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1(v_keys_1339_, v_v_1340_, v_node_1392_, v___x_1396_, v___x_1397_, v_x_1344_);
lean_inc_ref(v_newNode_1398_);
v___x_1399_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1398_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v___x_1401_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v_newNode_1398_);
v___x_1401_ = v___x_1394_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_newNode_1398_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
v___y_1360_ = v___x_1401_;
goto v___jp_1359_;
}
}
else
{
lean_object* v_val_1403_; lean_object* v_fst_1404_; lean_object* v_snd_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v_newNode_1398_);
lean_del_object(v___x_1394_);
v_val_1403_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_val_1403_);
lean_dec_ref_known(v___x_1399_, 1);
v_fst_1404_ = lean_ctor_get(v_val_1403_, 0);
v_snd_1405_ = lean_ctor_get(v_val_1403_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_val_1403_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v_val_1403_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_snd_1405_);
lean_inc(v_fst_1404_);
lean_dec(v_val_1403_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_fst_1404_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_snd_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
v___y_1360_ = v___x_1410_;
goto v___jp_1359_;
}
}
}
}
}
default: 
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___lam__0(v_keys_1339_, v_v_1340_, v___x_1414_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_dec(v_x_1344_);
v___y_1360_ = v_v_1356_;
goto v___jp_1359_;
}
else
{
lean_object* v_val_1416_; lean_object* v___x_1417_; 
v_val_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v_x_1344_);
lean_ctor_set(v___x_1417_, 1, v_val_1416_);
v___y_1360_ = v___x_1417_;
goto v___jp_1359_;
}
}
}
v___jp_1359_:
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1361_ = lean_array_fset(v_xs_x27_1358_, v_j_1350_, v___y_1360_);
lean_dec(v_j_1350_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1361_);
v___x_1363_ = v___x_1354_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_object* v_ks_1420_; lean_object* v_vs_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1454_; 
v_ks_1420_ = lean_ctor_get(v_x_1341_, 0);
v_vs_1421_ = lean_ctor_get(v_x_1341_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_x_1341_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1423_ = v_x_1341_;
v_isShared_1424_ = v_isSharedCheck_1454_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_vs_1421_);
lean_inc(v_ks_1420_);
lean_dec(v_x_1341_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1454_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4(v_ks_1420_, v_x_1344_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v___x_1427_; 
if (v_isShared_1424_ == 0)
{
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_ks_1420_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_vs_1421_);
v___x_1427_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_box(0);
v___x_1429_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___lam__0(v_keys_1339_, v_v_1340_, v___x_1428_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_dec(v_x_1344_);
return v___x_1427_;
}
else
{
lean_object* v_val_1430_; lean_object* v___x_1431_; 
v_val_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_val_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg(v___x_1427_, v_x_1342_, v_x_1343_, v_x_1344_, v_val_1430_);
return v___x_1431_;
}
}
}
else
{
lean_object* v_val_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1453_; 
v_val_1433_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1435_ = v___x_1425_;
v_isShared_1436_ = v_isSharedCheck_1453_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_val_1433_);
lean_dec(v___x_1425_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1453_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_v_x27_1437_; lean_object* v_keys_1438_; lean_object* v_vals_1439_; lean_object* v___x_1441_; 
v_v_x27_1437_ = lean_array_fget(v_vs_1421_, v_val_1433_);
lean_inc(v_val_1433_);
v_keys_1438_ = l_Array_eraseIdx___redArg(v_ks_1420_, v_val_1433_);
v_vals_1439_ = l_Array_eraseIdx___redArg(v_vs_1421_, v_val_1433_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v_v_x27_1437_);
v___x_1441_ = v___x_1435_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_v_x27_1437_);
v___x_1441_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___lam__0(v_keys_1339_, v_v_1340_, v___x_1441_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v___x_1444_; 
lean_dec(v_x_1344_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_vals_1439_);
lean_ctor_set(v___x_1423_, 0, v_keys_1438_);
v___x_1444_ = v___x_1423_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_keys_1438_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_vals_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
else
{
lean_object* v_val_1446_; lean_object* v_keys_1447_; lean_object* v_vals_1448_; lean_object* v___x_1450_; 
v_val_1446_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_val_1446_);
lean_dec_ref_known(v___x_1442_, 1);
v_keys_1447_ = lean_array_push(v_keys_1438_, v_x_1344_);
v_vals_1448_ = lean_array_push(v_vals_1439_, v_val_1446_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_vals_1448_);
lean_ctor_set(v___x_1423_, 0, v_keys_1447_);
v___x_1450_ = v___x_1423_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_keys_1447_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_vals_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___boxed(lean_object* v_keys_1455_, lean_object* v_v_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v_x_1460_){
_start:
{
size_t v_x_2116__boxed_1461_; size_t v_x_2117__boxed_1462_; lean_object* v_res_1463_; 
v_x_2116__boxed_1461_ = lean_unbox_usize(v_x_1458_);
lean_dec(v_x_1458_);
v_x_2117__boxed_1462_ = lean_unbox_usize(v_x_1459_);
lean_dec(v_x_1459_);
v_res_1463_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1(v_keys_1455_, v_v_1456_, v_x_1457_, v_x_2116__boxed_1461_, v_x_2117__boxed_1462_, v_x_1460_);
lean_dec_ref(v_keys_1455_);
return v_res_1463_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1467_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2));
v___x_1468_ = lean_unsigned_to_nat(23u);
v___x_1469_ = lean_unsigned_to_nat(166u);
v___x_1470_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1));
v___x_1471_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0));
v___x_1472_ = l_mkPanicMessageWithDecl(v___x_1471_, v___x_1470_, v___x_1469_, v___x_1468_, v___x_1467_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(lean_object* v_d_1473_, lean_object* v_keys_1474_, lean_object* v_v_1475_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = lean_array_get_size(v_keys_1474_);
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_nat_dec_eq(v___x_1476_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v_k_1480_; uint64_t v___x_1481_; size_t v_h_1482_; size_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1479_ = lean_box(0);
v_k_1480_ = lean_array_get_borrowed(v___x_1479_, v_keys_1474_, v___x_1477_);
v___x_1481_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1480_);
v_h_1482_ = lean_uint64_to_usize(v___x_1481_);
v___x_1483_ = ((size_t)1ULL);
lean_inc(v_k_1480_);
v___x_1484_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1(v_keys_1474_, v_v_1475_, v_d_1473_, v_h_1482_, v___x_1483_, v_k_1480_);
return v___x_1484_;
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref(v_v_1475_);
lean_dec_ref(v_d_1473_);
v___x_1485_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3);
v___x_1486_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v___x_1485_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___boxed(lean_object* v_d_1487_, lean_object* v_keys_1488_, lean_object* v_v_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(v_d_1487_, v_keys_1488_, v_v_1489_);
lean_dec_ref(v_keys_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(lean_object* v_d_1491_, lean_object* v_e_1492_){
_start:
{
lean_object* v_specs_1493_; lean_object* v_erased_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1503_; 
v_specs_1493_ = lean_ctor_get(v_d_1491_, 0);
v_erased_1494_ = lean_ctor_get(v_d_1491_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_d_1491_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1496_ = v_d_1491_;
v_isShared_1497_ = v_isSharedCheck_1503_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_erased_1494_);
lean_inc(v_specs_1493_);
lean_dec(v_d_1491_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1503_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_keys_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
v_keys_1498_ = lean_ctor_get(v_e_1492_, 0);
lean_inc_ref(v_keys_1498_);
v___x_1499_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(v_specs_1493_, v_keys_1498_, v_e_1492_);
lean_dec_ref(v_keys_1498_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1499_);
v___x_1501_ = v___x_1496_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_erased_1494_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1504_, lean_object* v_x_1505_, size_t v_x_1506_, size_t v_x_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg(v_x_1505_, v_x_1506_, v_x_1507_, v_x_1508_, v_x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1511_, lean_object* v_x_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_){
_start:
{
size_t v_x_2392__boxed_1517_; size_t v_x_2393__boxed_1518_; lean_object* v_res_1519_; 
v_x_2392__boxed_1517_ = lean_unbox_usize(v_x_1513_);
lean_dec(v_x_1513_);
v_x_2393__boxed_1518_ = lean_unbox_usize(v_x_1514_);
lean_dec(v_x_1514_);
v_res_1519_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5(v_00_u03b2_1511_, v_x_1512_, v_x_2392__boxed_1517_, v_x_2393__boxed_1518_, v_x_1515_, v_x_1516_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1520_, lean_object* v_keys_1521_, lean_object* v_v_1522_, lean_object* v_k_1523_, lean_object* v_as_1524_, lean_object* v_k_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1520_, v_keys_1521_, v_v_1522_, v_k_1523_, v_as_1524_, v_k_1525_, v_x_1526_, v_x_1527_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_1531_, lean_object* v_keys_1532_, lean_object* v_v_1533_, lean_object* v_k_1534_, lean_object* v_as_1535_, lean_object* v_k_1536_, lean_object* v_x_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2_spec__5(v_x_1531_, v_keys_1532_, v_v_1533_, v_k_1534_, v_as_1535_, v_k_1536_, v_x_1537_, v_x_1538_, v_x_1539_, v_x_1540_);
lean_dec_ref(v_k_1536_);
lean_dec_ref(v_keys_1532_);
lean_dec(v_x_1531_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_1542_, lean_object* v_n_1543_, lean_object* v_k_1544_, lean_object* v_v_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10___redArg(v_n_1543_, v_k_1544_, v_v_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1547_, size_t v_depth_1548_, lean_object* v_keys_1549_, lean_object* v_vals_1550_, lean_object* v_heq_1551_, lean_object* v_i_1552_, lean_object* v_entries_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11___redArg(v_depth_1548_, v_keys_1549_, v_vals_1550_, v_i_1552_, v_entries_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1555_, lean_object* v_depth_1556_, lean_object* v_keys_1557_, lean_object* v_vals_1558_, lean_object* v_heq_1559_, lean_object* v_i_1560_, lean_object* v_entries_1561_){
_start:
{
size_t v_depth_boxed_1562_; lean_object* v_res_1563_; 
v_depth_boxed_1562_ = lean_unbox_usize(v_depth_1556_);
lean_dec(v_depth_1556_);
v_res_1563_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__11(v_00_u03b2_1555_, v_depth_boxed_1562_, v_keys_1557_, v_vals_1558_, v_heq_1559_, v_i_1560_, v_entries_1561_);
lean_dec_ref(v_vals_1558_);
lean_dec_ref(v_keys_1557_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10_spec__11(lean_object* v_00_u03b2_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5_spec__10_spec__11___redArg(v_x_1565_, v_x_1566_, v_x_1567_, v_x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1570_, lean_object* v_i_1571_, lean_object* v_k_1572_){
_start:
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = lean_array_get_size(v_keys_1570_);
v___x_1574_ = lean_nat_dec_lt(v_i_1571_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_dec_ref(v_k_1572_);
lean_dec(v_i_1571_);
return v___x_1574_;
}
else
{
lean_object* v_k_x27_1575_; uint8_t v___x_1576_; 
v_k_x27_1575_ = lean_array_fget_borrowed(v_keys_1570_, v_i_1571_);
lean_inc(v_k_x27_1575_);
lean_inc_ref(v_k_1572_);
v___x_1576_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_k_1572_, v_k_x27_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_unsigned_to_nat(1u);
v___x_1578_ = lean_nat_add(v_i_1571_, v___x_1577_);
lean_dec(v_i_1571_);
v_i_1571_ = v___x_1578_;
goto _start;
}
else
{
lean_dec_ref(v_k_1572_);
lean_dec(v_i_1571_);
return v___x_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1580_, lean_object* v_i_1581_, lean_object* v_k_1582_){
_start:
{
uint8_t v_res_1583_; lean_object* v_r_1584_; 
v_res_1583_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_1580_, v_i_1581_, v_k_1582_);
lean_dec_ref(v_keys_1580_);
v_r_1584_ = lean_box(v_res_1583_);
return v_r_1584_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(lean_object* v_x_1585_, size_t v_x_1586_, lean_object* v_x_1587_){
_start:
{
if (lean_obj_tag(v_x_1585_) == 0)
{
lean_object* v_es_1588_; lean_object* v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; lean_object* v_j_1593_; lean_object* v___x_1594_; 
v_es_1588_ = lean_ctor_get(v_x_1585_, 0);
lean_inc_ref(v_es_1588_);
lean_dec_ref_known(v_x_1585_, 1);
v___x_1589_ = lean_box(2);
v___x_1590_ = ((size_t)5ULL);
v___x_1591_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1);
v___x_1592_ = lean_usize_land(v_x_1586_, v___x_1591_);
v_j_1593_ = lean_usize_to_nat(v___x_1592_);
v___x_1594_ = lean_array_get(v___x_1589_, v_es_1588_, v_j_1593_);
lean_dec(v_j_1593_);
lean_dec_ref(v_es_1588_);
switch(lean_obj_tag(v___x_1594_))
{
case 0:
{
lean_object* v_key_1595_; uint8_t v___x_1596_; 
v_key_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_key_1595_);
lean_dec_ref_known(v___x_1594_, 2);
v___x_1596_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1587_, v_key_1595_);
return v___x_1596_;
}
case 1:
{
lean_object* v_node_1597_; size_t v___x_1598_; 
v_node_1597_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_node_1597_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1598_ = lean_usize_shift_right(v_x_1586_, v___x_1590_);
v_x_1585_ = v_node_1597_;
v_x_1586_ = v___x_1598_;
goto _start;
}
default: 
{
uint8_t v___x_1600_; 
lean_dec_ref(v_x_1587_);
v___x_1600_ = 0;
return v___x_1600_;
}
}
}
else
{
lean_object* v_ks_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v_ks_1601_ = lean_ctor_get(v_x_1585_, 0);
lean_inc_ref(v_ks_1601_);
lean_dec_ref_known(v_x_1585_, 2);
v___x_1602_ = lean_unsigned_to_nat(0u);
v___x_1603_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_ks_1601_, v___x_1602_, v_x_1587_);
lean_dec_ref(v_ks_1601_);
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg___boxed(lean_object* v_x_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_){
_start:
{
size_t v_x_146__boxed_1607_; uint8_t v_res_1608_; lean_object* v_r_1609_; 
v_x_146__boxed_1607_ = lean_unbox_usize(v_x_1605_);
lean_dec(v_x_1605_);
v_res_1608_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_1604_, v_x_146__boxed_1607_, v_x_1606_);
v_r_1609_ = lean_box(v_res_1608_);
return v_r_1609_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
uint64_t v___y_1613_; lean_object* v___y_1617_; lean_object* v_declName_1620_; 
v_declName_1620_ = lean_ctor_get(v_x_1611_, 0);
lean_inc(v_declName_1620_);
v___y_1617_ = v_declName_1620_;
goto v___jp_1616_;
v___jp_1612_:
{
size_t v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = lean_uint64_to_usize(v___y_1613_);
v___x_1615_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_1610_, v___x_1614_, v_x_1611_);
return v___x_1615_;
}
v___jp_1616_:
{
if (lean_obj_tag(v___y_1617_) == 0)
{
uint64_t v___x_1618_; 
v___x_1618_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_1613_ = v___x_1618_;
goto v___jp_1612_;
}
else
{
uint64_t v_hash_1619_; 
v_hash_1619_ = lean_ctor_get_uint64(v___y_1617_, sizeof(void*)*2);
lean_dec(v___y_1617_);
v___y_1613_ = v_hash_1619_;
goto v___jp_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg___boxed(lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
uint8_t v_res_1623_; lean_object* v_r_1624_; 
v_res_1623_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_1621_, v_x_1622_);
v_r_1624_ = lean_box(v_res_1623_);
return v_r_1624_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(lean_object* v_d_1625_, lean_object* v_thmId_1626_){
_start:
{
lean_object* v_erased_1627_; uint8_t v___x_1628_; 
v_erased_1627_ = lean_ctor_get(v_d_1625_, 1);
lean_inc_ref(v_erased_1627_);
lean_dec_ref(v_d_1625_);
v___x_1628_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_erased_1627_, v_thmId_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased___boxed(lean_object* v_d_1629_, lean_object* v_thmId_1630_){
_start:
{
uint8_t v_res_1631_; lean_object* v_r_1632_; 
v_res_1631_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_d_1629_, v_thmId_1630_);
v_r_1632_ = lean_box(v_res_1631_);
return v_r_1632_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(lean_object* v_00_u03b2_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___boxed(lean_object* v_00_u03b2_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
uint8_t v_res_1640_; lean_object* v_r_1641_; 
v_res_1640_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(v_00_u03b2_1637_, v_x_1638_, v_x_1639_);
v_r_1641_ = lean_box(v_res_1640_);
return v_r_1641_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(lean_object* v_00_u03b2_1642_, lean_object* v_x_1643_, size_t v_x_1644_, lean_object* v_x_1645_){
_start:
{
uint8_t v___x_1646_; 
v___x_1646_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_1643_, v_x_1644_, v_x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_){
_start:
{
size_t v_x_228__boxed_1651_; uint8_t v_res_1652_; lean_object* v_r_1653_; 
v_x_228__boxed_1651_ = lean_unbox_usize(v_x_1649_);
lean_dec(v_x_1649_);
v_res_1652_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(v_00_u03b2_1647_, v_x_1648_, v_x_228__boxed_1651_, v_x_1650_);
v_r_1653_ = lean_box(v_res_1652_);
return v_r_1653_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1654_, lean_object* v_keys_1655_, lean_object* v_vals_1656_, lean_object* v_heq_1657_, lean_object* v_i_1658_, lean_object* v_k_1659_){
_start:
{
uint8_t v___x_1660_; 
v___x_1660_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_1655_, v_i_1658_, v_k_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1661_, lean_object* v_keys_1662_, lean_object* v_vals_1663_, lean_object* v_heq_1664_, lean_object* v_i_1665_, lean_object* v_k_1666_){
_start:
{
uint8_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(v_00_u03b2_1661_, v_keys_1662_, v_vals_1663_, v_heq_1664_, v_i_1665_, v_k_1666_);
lean_dec_ref(v_vals_1663_);
lean_dec_ref(v_keys_1662_);
v_r_1668_ = lean_box(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v_ks_1673_; lean_object* v_vs_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1698_; 
v_ks_1673_ = lean_ctor_get(v_x_1669_, 0);
v_vs_1674_ = lean_ctor_get(v_x_1669_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_x_1669_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1676_ = v_x_1669_;
v_isShared_1677_ = v_isSharedCheck_1698_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_vs_1674_);
lean_inc(v_ks_1673_);
lean_dec(v_x_1669_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1698_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1678_ = lean_array_get_size(v_ks_1673_);
v___x_1679_ = lean_nat_dec_lt(v_x_1670_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
lean_dec(v_x_1670_);
v___x_1680_ = lean_array_push(v_ks_1673_, v_x_1671_);
v___x_1681_ = lean_array_push(v_vs_1674_, v_x_1672_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v___x_1681_);
lean_ctor_set(v___x_1676_, 0, v___x_1680_);
v___x_1683_ = v___x_1676_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
else
{
lean_object* v_k_x27_1685_; uint8_t v___x_1686_; 
v_k_x27_1685_ = lean_array_fget_borrowed(v_ks_1673_, v_x_1670_);
lean_inc(v_k_x27_1685_);
lean_inc_ref(v_x_1671_);
v___x_1686_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1671_, v_k_x27_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1688_; 
if (v_isShared_1677_ == 0)
{
v___x_1688_ = v___x_1676_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_ks_1673_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_vs_1674_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_nat_add(v_x_1670_, v___x_1689_);
lean_dec(v_x_1670_);
v_x_1669_ = v___x_1688_;
v_x_1670_ = v___x_1690_;
goto _start;
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1693_ = lean_array_fset(v_ks_1673_, v_x_1670_, v_x_1671_);
v___x_1694_ = lean_array_fset(v_vs_1674_, v_x_1670_, v_x_1672_);
lean_dec(v_x_1670_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v___x_1694_);
lean_ctor_set(v___x_1676_, 0, v___x_1693_);
v___x_1696_ = v___x_1676_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1699_, lean_object* v_k_1700_, lean_object* v_v_1701_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = lean_unsigned_to_nat(0u);
v___x_1703_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1699_, v___x_1702_, v_k_1700_, v_v_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(lean_object* v_x_1705_, size_t v_x_1706_, size_t v_x_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_){
_start:
{
if (lean_obj_tag(v_x_1705_) == 0)
{
lean_object* v_es_1710_; size_t v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; lean_object* v_j_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_es_1710_ = lean_ctor_get(v_x_1705_, 0);
v___x_1711_ = ((size_t)5ULL);
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1);
v___x_1714_ = lean_usize_land(v_x_1706_, v___x_1713_);
v_j_1715_ = lean_usize_to_nat(v___x_1714_);
v___x_1716_ = lean_array_get_size(v_es_1710_);
v___x_1717_ = lean_nat_dec_lt(v_j_1715_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_dec(v_j_1715_);
lean_dec(v_x_1709_);
lean_dec_ref(v_x_1708_);
return v_x_1705_;
}
else
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1754_; 
lean_inc_ref(v_es_1710_);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_x_1705_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v_x_1705_, 0);
lean_dec(v_unused_1755_);
v___x_1719_ = v_x_1705_;
v_isShared_1720_ = v_isSharedCheck_1754_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v_x_1705_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1754_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v_v_1721_; lean_object* v___x_1722_; lean_object* v_xs_x27_1723_; lean_object* v___y_1725_; 
v_v_1721_ = lean_array_fget(v_es_1710_, v_j_1715_);
v___x_1722_ = lean_box(0);
v_xs_x27_1723_ = lean_array_fset(v_es_1710_, v_j_1715_, v___x_1722_);
switch(lean_obj_tag(v_v_1721_))
{
case 0:
{
lean_object* v_key_1730_; lean_object* v_val_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1741_; 
v_key_1730_ = lean_ctor_get(v_v_1721_, 0);
v_val_1731_ = lean_ctor_get(v_v_1721_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_v_1721_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1733_ = v_v_1721_;
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_val_1731_);
lean_inc(v_key_1730_);
lean_dec(v_v_1721_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
uint8_t v___x_1735_; 
lean_inc(v_key_1730_);
lean_inc_ref(v_x_1708_);
v___x_1735_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1708_, v_key_1730_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_del_object(v___x_1733_);
v___x_1736_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1730_, v_val_1731_, v_x_1708_, v_x_1709_);
v___x_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
v___y_1725_ = v___x_1737_;
goto v___jp_1724_;
}
else
{
lean_object* v___x_1739_; 
lean_dec(v_val_1731_);
lean_dec(v_key_1730_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v_x_1709_);
lean_ctor_set(v___x_1733_, 0, v_x_1708_);
v___x_1739_ = v___x_1733_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_x_1708_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_x_1709_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
v___y_1725_ = v___x_1739_;
goto v___jp_1724_;
}
}
}
}
case 1:
{
lean_object* v_node_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1752_; 
v_node_1742_ = lean_ctor_get(v_v_1721_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_v_1721_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1744_ = v_v_1721_;
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_node_1742_);
lean_dec(v_v_1721_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
size_t v___x_1746_; size_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1746_ = lean_usize_shift_right(v_x_1706_, v___x_1711_);
v___x_1747_ = lean_usize_add(v_x_1707_, v___x_1712_);
v___x_1748_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_node_1742_, v___x_1746_, v___x_1747_, v_x_1708_, v_x_1709_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1748_);
v___x_1750_ = v___x_1744_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
v___y_1725_ = v___x_1750_;
goto v___jp_1724_;
}
}
}
default: 
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_x_1708_);
lean_ctor_set(v___x_1753_, 1, v_x_1709_);
v___y_1725_ = v___x_1753_;
goto v___jp_1724_;
}
}
v___jp_1724_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = lean_array_fset(v_xs_x27_1723_, v_j_1715_, v___y_1725_);
lean_dec(v_j_1715_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1726_);
v___x_1728_ = v___x_1719_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
}
else
{
lean_object* v_ks_1756_; lean_object* v_vs_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1777_; 
v_ks_1756_ = lean_ctor_get(v_x_1705_, 0);
v_vs_1757_ = lean_ctor_get(v_x_1705_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_x_1705_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1759_ = v_x_1705_;
v_isShared_1760_ = v_isSharedCheck_1777_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_vs_1757_);
lean_inc(v_ks_1756_);
lean_dec(v_x_1705_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1777_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_ks_1756_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_vs_1757_);
v___x_1762_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v_newNode_1763_; uint8_t v___y_1765_; size_t v___x_1771_; uint8_t v___x_1772_; 
v_newNode_1763_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v___x_1762_, v_x_1708_, v_x_1709_);
v___x_1771_ = ((size_t)7ULL);
v___x_1772_ = lean_usize_dec_le(v___x_1771_, v_x_1707_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1763_);
v___x_1774_ = lean_unsigned_to_nat(4u);
v___x_1775_ = lean_nat_dec_lt(v___x_1773_, v___x_1774_);
lean_dec(v___x_1773_);
v___y_1765_ = v___x_1775_;
goto v___jp_1764_;
}
else
{
v___y_1765_ = v___x_1772_;
goto v___jp_1764_;
}
v___jp_1764_:
{
if (v___y_1765_ == 0)
{
lean_object* v_ks_1766_; lean_object* v_vs_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_ks_1766_ = lean_ctor_get(v_newNode_1763_, 0);
lean_inc_ref(v_ks_1766_);
v_vs_1767_ = lean_ctor_get(v_newNode_1763_, 1);
lean_inc_ref(v_vs_1767_);
lean_dec_ref(v_newNode_1763_);
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0);
v___x_1770_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_x_1707_, v_ks_1766_, v_vs_1767_, v___x_1768_, v___x_1769_);
lean_dec_ref(v_vs_1767_);
lean_dec_ref(v_ks_1766_);
return v___x_1770_;
}
else
{
return v_newNode_1763_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(size_t v_depth_1778_, lean_object* v_keys_1779_, lean_object* v_vals_1780_, lean_object* v_i_1781_, lean_object* v_entries_1782_){
_start:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = lean_array_get_size(v_keys_1779_);
v___x_1784_ = lean_nat_dec_lt(v_i_1781_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_dec(v_i_1781_);
return v_entries_1782_;
}
else
{
lean_object* v_k_1785_; lean_object* v_v_1786_; uint64_t v___y_1788_; lean_object* v___y_1800_; lean_object* v_declName_1803_; 
v_k_1785_ = lean_array_fget_borrowed(v_keys_1779_, v_i_1781_);
v_v_1786_ = lean_array_fget_borrowed(v_vals_1780_, v_i_1781_);
v_declName_1803_ = lean_ctor_get(v_k_1785_, 0);
lean_inc(v_declName_1803_);
v___y_1800_ = v_declName_1803_;
goto v___jp_1799_;
v___jp_1787_:
{
size_t v_h_1789_; size_t v___x_1790_; lean_object* v___x_1791_; size_t v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; size_t v_h_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_h_1789_ = lean_uint64_to_usize(v___y_1788_);
v___x_1790_ = ((size_t)5ULL);
v___x_1791_ = lean_unsigned_to_nat(1u);
v___x_1792_ = ((size_t)1ULL);
v___x_1793_ = lean_usize_sub(v_depth_1778_, v___x_1792_);
v___x_1794_ = lean_usize_mul(v___x_1790_, v___x_1793_);
v_h_1795_ = lean_usize_shift_right(v_h_1789_, v___x_1794_);
v___x_1796_ = lean_nat_add(v_i_1781_, v___x_1791_);
lean_dec(v_i_1781_);
lean_inc(v_v_1786_);
lean_inc(v_k_1785_);
v___x_1797_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_entries_1782_, v_h_1795_, v_depth_1778_, v_k_1785_, v_v_1786_);
v_i_1781_ = v___x_1796_;
v_entries_1782_ = v___x_1797_;
goto _start;
}
v___jp_1799_:
{
if (lean_obj_tag(v___y_1800_) == 0)
{
uint64_t v___x_1801_; 
v___x_1801_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_1788_ = v___x_1801_;
goto v___jp_1787_;
}
else
{
uint64_t v_hash_1802_; 
v_hash_1802_ = lean_ctor_get_uint64(v___y_1800_, sizeof(void*)*2);
lean_dec(v___y_1800_);
v___y_1788_ = v_hash_1802_;
goto v___jp_1787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1804_, lean_object* v_keys_1805_, lean_object* v_vals_1806_, lean_object* v_i_1807_, lean_object* v_entries_1808_){
_start:
{
size_t v_depth_boxed_1809_; lean_object* v_res_1810_; 
v_depth_boxed_1809_ = lean_unbox_usize(v_depth_1804_);
lean_dec(v_depth_1804_);
v_res_1810_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1809_, v_keys_1805_, v_vals_1806_, v_i_1807_, v_entries_1808_);
lean_dec_ref(v_vals_1806_);
lean_dec_ref(v_keys_1805_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
size_t v_x_400__boxed_1816_; size_t v_x_401__boxed_1817_; lean_object* v_res_1818_; 
v_x_400__boxed_1816_ = lean_unbox_usize(v_x_1812_);
lean_dec(v_x_1812_);
v_x_401__boxed_1817_ = lean_unbox_usize(v_x_1813_);
lean_dec(v_x_1813_);
v_res_1818_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_1811_, v_x_400__boxed_1816_, v_x_401__boxed_1817_, v_x_1814_, v_x_1815_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(lean_object* v_x_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
uint64_t v___y_1823_; lean_object* v___y_1828_; lean_object* v_declName_1831_; 
v_declName_1831_ = lean_ctor_get(v_x_1820_, 0);
lean_inc(v_declName_1831_);
v___y_1828_ = v_declName_1831_;
goto v___jp_1827_;
v___jp_1822_:
{
size_t v___x_1824_; size_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_uint64_to_usize(v___y_1823_);
v___x_1825_ = ((size_t)1ULL);
v___x_1826_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_1819_, v___x_1824_, v___x_1825_, v_x_1820_, v_x_1821_);
return v___x_1826_;
}
v___jp_1827_:
{
if (lean_obj_tag(v___y_1828_) == 0)
{
uint64_t v___x_1829_; 
v___x_1829_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_1823_ = v___x_1829_;
goto v___jp_1822_;
}
else
{
uint64_t v_hash_1830_; 
v_hash_1830_ = lean_ctor_get_uint64(v___y_1828_, sizeof(void*)*2);
lean_dec(v___y_1828_);
v___y_1823_ = v_hash_1830_;
goto v___jp_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(lean_object* v_d_1832_, lean_object* v_thmId_1833_){
_start:
{
lean_object* v_specs_1834_; lean_object* v_erased_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1844_; 
v_specs_1834_ = lean_ctor_get(v_d_1832_, 0);
v_erased_1835_ = lean_ctor_get(v_d_1832_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_d_1832_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1837_ = v_d_1832_;
v_isShared_1838_ = v_isSharedCheck_1844_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_erased_1835_);
lean_inc(v_specs_1834_);
lean_dec(v_d_1832_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1844_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1839_ = lean_box(0);
v___x_1840_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_erased_1835_, v_thmId_1833_, v___x_1839_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 1, v___x_1840_);
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_specs_1834_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0(lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_x_1846_, v_x_1847_, v_x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(lean_object* v_00_u03b2_1850_, lean_object* v_x_1851_, size_t v_x_1852_, size_t v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_1851_, v_x_1852_, v_x_1853_, v_x_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_){
_start:
{
size_t v_x_618__boxed_1863_; size_t v_x_619__boxed_1864_; lean_object* v_res_1865_; 
v_x_618__boxed_1863_ = lean_unbox_usize(v_x_1859_);
lean_dec(v_x_1859_);
v_x_619__boxed_1864_ = lean_unbox_usize(v_x_1860_);
lean_dec(v_x_1860_);
v_res_1865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(v_00_u03b2_1857_, v_x_1858_, v_x_618__boxed_1863_, v_x_619__boxed_1864_, v_x_1861_, v_x_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1866_, lean_object* v_n_1867_, lean_object* v_k_1868_, lean_object* v_v_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v_n_1867_, v_k_1868_, v_v_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1871_, size_t v_depth_1872_, lean_object* v_keys_1873_, lean_object* v_vals_1874_, lean_object* v_heq_1875_, lean_object* v_i_1876_, lean_object* v_entries_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_1872_, v_keys_1873_, v_vals_1874_, v_i_1876_, v_entries_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1879_, lean_object* v_depth_1880_, lean_object* v_keys_1881_, lean_object* v_vals_1882_, lean_object* v_heq_1883_, lean_object* v_i_1884_, lean_object* v_entries_1885_){
_start:
{
size_t v_depth_boxed_1886_; lean_object* v_res_1887_; 
v_depth_boxed_1886_ = lean_unbox_usize(v_depth_1880_);
lean_dec(v_depth_1880_);
v_res_1887_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(v_00_u03b2_1879_, v_depth_boxed_1886_, v_keys_1881_, v_vals_1882_, v_heq_1883_, v_i_1884_, v_entries_1885_);
lean_dec_ref(v_vals_1882_);
lean_dec_ref(v_keys_1881_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1889_, v_x_1890_, v_x_1891_, v_x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(lean_object* v_a_1894_, lean_object* v_as_1895_, size_t v_i_1896_, size_t v_stop_1897_){
_start:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_usize_dec_eq(v_i_1896_, v_stop_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = lean_array_uget_borrowed(v_as_1895_, v_i_1896_);
v___x_1900_ = lean_expr_eqv(v_a_1894_, v___x_1899_);
if (v___x_1900_ == 0)
{
size_t v___x_1901_; size_t v___x_1902_; 
v___x_1901_ = ((size_t)1ULL);
v___x_1902_ = lean_usize_add(v_i_1896_, v___x_1901_);
v_i_1896_ = v___x_1902_;
goto _start;
}
else
{
return v___x_1900_;
}
}
else
{
uint8_t v___x_1904_; 
v___x_1904_ = 0;
return v___x_1904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0___boxed(lean_object* v_a_1905_, lean_object* v_as_1906_, lean_object* v_i_1907_, lean_object* v_stop_1908_){
_start:
{
size_t v_i_boxed_1909_; size_t v_stop_boxed_1910_; uint8_t v_res_1911_; lean_object* v_r_1912_; 
v_i_boxed_1909_ = lean_unbox_usize(v_i_1907_);
lean_dec(v_i_1907_);
v_stop_boxed_1910_ = lean_unbox_usize(v_stop_1908_);
lean_dec(v_stop_1908_);
v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(v_a_1905_, v_as_1906_, v_i_boxed_1909_, v_stop_boxed_1910_);
lean_dec_ref(v_as_1906_);
lean_dec_ref(v_a_1905_);
v_r_1912_ = lean_box(v_res_1911_);
return v_r_1912_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(lean_object* v_as_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = lean_array_get_size(v_as_1913_);
v___x_1917_ = lean_nat_dec_lt(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
return v___x_1917_;
}
else
{
if (v___x_1917_ == 0)
{
return v___x_1917_;
}
else
{
size_t v___x_1918_; size_t v___x_1919_; uint8_t v___x_1920_; 
v___x_1918_ = ((size_t)0ULL);
v___x_1919_ = lean_usize_of_nat(v___x_1916_);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(v_a_1914_, v_as_1913_, v___x_1918_, v___x_1919_);
return v___x_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0___boxed(lean_object* v_as_1921_, lean_object* v_a_1922_){
_start:
{
uint8_t v_res_1923_; lean_object* v_r_1924_; 
v_res_1923_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_as_1921_, v_a_1922_);
lean_dec_ref(v_a_1922_);
lean_dec_ref(v_as_1921_);
v_r_1924_ = lean_box(v_res_1923_);
return v_r_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(lean_object* v_xs_1928_, lean_object* v_e_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_ty_1936_; lean_object* v_b_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; uint8_t v___x_1954_; 
v___x_1954_ = l_Lean_Expr_hasExprMVar(v_e_1929_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
return v___x_1956_;
}
else
{
switch(lean_obj_tag(v_e_1929_))
{
case 5:
{
lean_object* v_fn_1957_; lean_object* v_arg_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v_fn_1957_ = lean_ctor_get(v_e_1929_, 0);
v_arg_1958_ = lean_ctor_get(v_e_1929_, 1);
v___x_1959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1));
v___x_1960_ = lean_unsigned_to_nat(3u);
v___x_1961_ = l_Lean_Expr_isAppOfArity(v_e_1929_, v___x_1959_, v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
v___x_1962_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1928_, v_fn_1957_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1928_, v_arg_1958_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_nat_add(v_a_1963_, v_a_1965_);
lean_dec(v_a_1965_);
lean_dec(v_a_1963_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_dec(v_a_1963_);
return v___x_1964_;
}
}
else
{
return v___x_1962_;
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_l_1990_; lean_object* v_r_1991_; uint8_t v___y_1993_; uint8_t v___y_2001_; uint8_t v___x_2005_; 
v___x_1974_ = l_Lean_Expr_appFn_x21(v_e_1929_);
v___x_1975_ = l_Lean_Expr_appArg_x21(v___x_1974_);
lean_dec_ref(v___x_1974_);
v___x_1976_ = l_Lean_Expr_appArg_x21(v_e_1929_);
v_l_1990_ = l_Lean_Expr_getAppFn_x27(v___x_1975_);
v_r_1991_ = l_Lean_Expr_getAppFn_x27(v___x_1976_);
v___x_2005_ = l_Lean_Expr_isMVar(v_l_1990_);
if (v___x_2005_ == 0)
{
v___y_2001_ = v___x_2005_;
goto v___jp_2000_;
}
else
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lean_Expr_hasLooseBVars(v___x_1976_);
v___y_2001_ = v___x_2006_;
goto v___jp_2000_;
}
v___jp_1977_:
{
lean_object* v___x_1978_; 
v___x_1978_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1928_, v___x_1975_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec_ref(v___x_1975_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1928_, v___x_1976_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec_ref(v___x_1976_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1989_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_1989_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1989_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_nat_add(v_a_1979_, v_a_1981_);
lean_dec(v_a_1981_);
lean_dec(v_a_1979_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1985_);
v___x_1987_ = v___x_1983_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
else
{
lean_dec(v_a_1979_);
return v___x_1980_;
}
}
else
{
lean_dec_ref(v___x_1976_);
return v___x_1978_;
}
}
v___jp_1992_:
{
if (v___y_1993_ == 0)
{
lean_dec_ref(v_r_1991_);
goto v___jp_1977_;
}
else
{
uint8_t v___x_1994_; 
v___x_1994_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_xs_1928_, v_r_1991_);
lean_dec_ref(v_r_1991_);
if (v___x_1994_ == 0)
{
goto v___jp_1977_;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec_ref(v___x_1976_);
lean_dec_ref(v___x_1975_);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
return v___x_1996_;
}
}
}
v___jp_1997_:
{
uint8_t v___x_1998_; 
v___x_1998_ = l_Lean_Expr_isMVar(v_r_1991_);
if (v___x_1998_ == 0)
{
v___y_1993_ = v___x_1998_;
goto v___jp_1992_;
}
else
{
uint8_t v___x_1999_; 
v___x_1999_ = l_Lean_Expr_hasLooseBVars(v___x_1975_);
v___y_1993_ = v___x_1999_;
goto v___jp_1992_;
}
}
v___jp_2000_:
{
if (v___y_2001_ == 0)
{
lean_dec_ref(v_l_1990_);
goto v___jp_1997_;
}
else
{
uint8_t v___x_2002_; 
v___x_2002_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_xs_1928_, v_l_1990_);
lean_dec_ref(v_l_1990_);
if (v___x_2002_ == 0)
{
goto v___jp_1997_;
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_dec_ref(v_r_1991_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v___x_1975_);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
return v___x_2004_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_2007_; lean_object* v_body_2008_; 
v_binderType_2007_ = lean_ctor_get(v_e_1929_, 1);
v_body_2008_ = lean_ctor_get(v_e_1929_, 2);
v_ty_1936_ = v_binderType_2007_;
v_b_1937_ = v_body_2008_;
v___y_1938_ = v_a_1930_;
v___y_1939_ = v_a_1931_;
v___y_1940_ = v_a_1932_;
v___y_1941_ = v_a_1933_;
goto v___jp_1935_;
}
case 7:
{
lean_object* v_binderType_2009_; lean_object* v_body_2010_; 
v_binderType_2009_ = lean_ctor_get(v_e_1929_, 1);
v_body_2010_ = lean_ctor_get(v_e_1929_, 2);
v_ty_1936_ = v_binderType_2009_;
v_b_1937_ = v_body_2010_;
v___y_1938_ = v_a_1930_;
v___y_1939_ = v_a_1931_;
v___y_1940_ = v_a_1932_;
v___y_1941_ = v_a_1933_;
goto v___jp_1935_;
}
case 8:
{
lean_object* v_type_2011_; lean_object* v_value_2012_; lean_object* v_body_2013_; lean_object* v___x_2014_; 
v_type_2011_ = lean_ctor_get(v_e_1929_, 1);
v_value_2012_ = lean_ctor_get(v_e_1929_, 2);
v_body_2013_ = lean_ctor_get(v_e_1929_, 3);
v___x_2014_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1928_, v_type_2011_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1928_, v_value_2012_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1928_, v_body_2013_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2028_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2023_ = lean_nat_add(v_a_2015_, v_a_2017_);
lean_dec(v_a_2017_);
lean_dec(v_a_2015_);
v___x_2024_ = lean_nat_add(v___x_2023_, v_a_2019_);
lean_dec(v_a_2019_);
lean_dec(v___x_2023_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2024_);
v___x_2026_ = v___x_2021_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_dec(v_a_2017_);
lean_dec(v_a_2015_);
return v___x_2018_;
}
}
else
{
lean_dec(v_a_2015_);
return v___x_2016_;
}
}
else
{
return v___x_2014_;
}
}
case 10:
{
lean_object* v_expr_2029_; 
v_expr_2029_ = lean_ctor_get(v_e_1929_, 1);
v_e_1929_ = v_expr_2029_;
goto _start;
}
case 11:
{
lean_object* v_struct_2031_; 
v_struct_2031_ = lean_ctor_get(v_e_1929_, 2);
v_e_1929_ = v_struct_2031_;
goto _start;
}
default: 
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
}
v___jp_1935_:
{
lean_object* v___x_1942_; 
v___x_1942_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1928_, v_ty_1936_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_1928_, v_b_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1953_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1953_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1953_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1949_ = lean_nat_add(v_a_1943_, v_a_1945_);
lean_dec(v_a_1945_);
lean_dec(v_a_1943_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1949_);
v___x_1951_ = v___x_1947_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
else
{
lean_dec(v_a_1943_);
return v___x_1944_;
}
}
else
{
return v___x_1942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___boxed(lean_object* v_xs_2035_, lean_object* v_e_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2035_, v_e_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec_ref(v_e_2036_);
lean_dec_ref(v_xs_2035_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(lean_object* v_xs_2043_, lean_object* v_e_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2043_, v_e_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars___boxed(lean_object* v_xs_2051_, lean_object* v_e_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(v_xs_2051_, v_e_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec_ref(v_e_2052_);
lean_dec_ref(v_xs_2051_);
return v_res_2058_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig(void){
_start:
{
lean_object* v___x_2059_; lean_object* v_config_2060_; uint8_t v_foApprox_2061_; uint8_t v_ctxApprox_2062_; uint8_t v_quasiPatternApprox_2063_; uint8_t v_constApprox_2064_; uint8_t v_isDefEqStuckEx_2065_; uint8_t v_unificationHints_2066_; uint8_t v_proofIrrelevance_2067_; uint8_t v_assignSyntheticOpaque_2068_; uint8_t v_offsetCnstrs_2069_; uint8_t v_transparency_2070_; uint8_t v_etaStruct_2071_; uint8_t v_univApprox_2072_; uint8_t v_zetaUnused_2073_; uint8_t v_zetaHave_2074_; uint8_t v___x_2075_; uint8_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2059_ = l_Lean_Meta_simpGlobalConfig;
v_config_2060_ = lean_ctor_get(v___x_2059_, 0);
v_foApprox_2061_ = lean_ctor_get_uint8(v_config_2060_, 0);
v_ctxApprox_2062_ = lean_ctor_get_uint8(v_config_2060_, 1);
v_quasiPatternApprox_2063_ = lean_ctor_get_uint8(v_config_2060_, 2);
v_constApprox_2064_ = lean_ctor_get_uint8(v_config_2060_, 3);
v_isDefEqStuckEx_2065_ = lean_ctor_get_uint8(v_config_2060_, 4);
v_unificationHints_2066_ = lean_ctor_get_uint8(v_config_2060_, 5);
v_proofIrrelevance_2067_ = lean_ctor_get_uint8(v_config_2060_, 6);
v_assignSyntheticOpaque_2068_ = lean_ctor_get_uint8(v_config_2060_, 7);
v_offsetCnstrs_2069_ = lean_ctor_get_uint8(v_config_2060_, 8);
v_transparency_2070_ = lean_ctor_get_uint8(v_config_2060_, 9);
v_etaStruct_2071_ = lean_ctor_get_uint8(v_config_2060_, 10);
v_univApprox_2072_ = lean_ctor_get_uint8(v_config_2060_, 11);
v_zetaUnused_2073_ = lean_ctor_get_uint8(v_config_2060_, 17);
v_zetaHave_2074_ = lean_ctor_get_uint8(v_config_2060_, 18);
v___x_2075_ = 1;
v___x_2076_ = 2;
v___x_2077_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2077_, 0, v_foApprox_2061_);
lean_ctor_set_uint8(v___x_2077_, 1, v_ctxApprox_2062_);
lean_ctor_set_uint8(v___x_2077_, 2, v_quasiPatternApprox_2063_);
lean_ctor_set_uint8(v___x_2077_, 3, v_constApprox_2064_);
lean_ctor_set_uint8(v___x_2077_, 4, v_isDefEqStuckEx_2065_);
lean_ctor_set_uint8(v___x_2077_, 5, v_unificationHints_2066_);
lean_ctor_set_uint8(v___x_2077_, 6, v_proofIrrelevance_2067_);
lean_ctor_set_uint8(v___x_2077_, 7, v_assignSyntheticOpaque_2068_);
lean_ctor_set_uint8(v___x_2077_, 8, v_offsetCnstrs_2069_);
lean_ctor_set_uint8(v___x_2077_, 9, v_transparency_2070_);
lean_ctor_set_uint8(v___x_2077_, 10, v_etaStruct_2071_);
lean_ctor_set_uint8(v___x_2077_, 11, v_univApprox_2072_);
lean_ctor_set_uint8(v___x_2077_, 12, v___x_2075_);
lean_ctor_set_uint8(v___x_2077_, 13, v___x_2075_);
lean_ctor_set_uint8(v___x_2077_, 14, v___x_2076_);
lean_ctor_set_uint8(v___x_2077_, 15, v___x_2075_);
lean_ctor_set_uint8(v___x_2077_, 16, v___x_2075_);
lean_ctor_set_uint8(v___x_2077_, 17, v_zetaUnused_2073_);
lean_ctor_set_uint8(v___x_2077_, 18, v_zetaHave_2074_);
v___x_2078_ = l_Lean_Meta_Config_toConfigWithKey(v___x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(lean_object* v_k_2079_, uint8_t v_allowLevelAssignments_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2080_, v_k_2079_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
v_a_2095_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2086_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2086_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg___boxed(lean_object* v_k_2103_, lean_object* v_allowLevelAssignments_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2110_; lean_object* v_res_2111_; 
v_allowLevelAssignments_boxed_2110_ = lean_unbox(v_allowLevelAssignments_2104_);
v_res_2111_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_2103_, v_allowLevelAssignments_boxed_2110_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(lean_object* v_00_u03b1_2112_, lean_object* v_k_2113_, uint8_t v_allowLevelAssignments_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_2113_, v_allowLevelAssignments_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___boxed(lean_object* v_00_u03b1_2121_, lean_object* v_k_2122_, lean_object* v_allowLevelAssignments_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2129_; lean_object* v_res_2130_; 
v_allowLevelAssignments_boxed_2129_ = lean_unbox(v_allowLevelAssignments_2123_);
v_res_2130_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(v_00_u03b1_2121_, v_k_2122_, v_allowLevelAssignments_boxed_2129_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(lean_object* v___x_2131_, lean_object* v___x_2132_, lean_object* v_fst_2133_, lean_object* v___x_2134_, lean_object* v_expr_2135_, lean_object* v_____r_2136_, lean_object* v_lastSuccess_2137_, lean_object* v_boundAssignments_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2144_ = lean_unsigned_to_nat(2u);
v___x_2145_ = lean_nat_sub(v___x_2131_, v___x_2144_);
v___x_2146_ = lean_nat_sub(v___x_2145_, v___x_2132_);
lean_dec(v___x_2145_);
v___x_2147_ = l_Lean_Expr_getRevArg_x21(v_fst_2133_, v___x_2146_);
v___x_2148_ = l_Lean_Meta_whnfR(v___x_2147_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2161_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2151_ = v___x_2148_;
v_isShared_2152_ = v_isSharedCheck_2161_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2161_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v_lastSuccess_2137_);
lean_ctor_set(v___x_2153_, 1, v_boundAssignments_2138_);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2134_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v_expr_2135_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v_a_2149_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2157_);
v___x_2159_ = v___x_2151_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_boundAssignments_2138_);
lean_dec(v_lastSuccess_2137_);
lean_dec_ref(v_expr_2135_);
lean_dec(v___x_2134_);
v_a_2162_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2148_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2148_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0___boxed(lean_object* v___x_2170_, lean_object* v___x_2171_, lean_object* v_fst_2172_, lean_object* v___x_2173_, lean_object* v_expr_2174_, lean_object* v_____r_2175_, lean_object* v_lastSuccess_2176_, lean_object* v_boundAssignments_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_2170_, v___x_2171_, v_fst_2172_, v___x_2173_, v_expr_2174_, v_____r_2175_, v_lastSuccess_2176_, v_boundAssignments_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v_fst_2172_);
lean_dec(v___x_2171_);
lean_dec(v___x_2170_);
return v_res_2183_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2191_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5);
v___x_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2194_);
return v___x_2196_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_unsigned_to_nat(32u);
v___x_2198_ = lean_mk_empty_array_with_capacity(v___x_2197_);
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8(void){
_start:
{
size_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2200_ = ((size_t)5ULL);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_unsigned_to_nat(32u);
v___x_2203_ = lean_mk_empty_array_with_capacity(v___x_2202_);
v___x_2204_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7);
v___x_2205_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___x_2203_);
lean_ctor_set(v___x_2205_, 2, v___x_2201_);
lean_ctor_set(v___x_2205_, 3, v___x_2201_);
lean_ctor_set_usize(v___x_2205_, 4, v___x_2200_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8);
v___x_2207_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5);
v___x_2208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
lean_ctor_set(v___x_2208_, 2, v___x_2207_);
lean_ctor_set(v___x_2208_, 3, v___x_2206_);
return v___x_2208_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9);
v___x_2210_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6);
v___x_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(lean_object* v_a_2212_, lean_object* v_xs_2213_, lean_object* v_a_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___y_2221_; lean_object* v_snd_2241_; lean_object* v_snd_2242_; lean_object* v_snd_2243_; lean_object* v_fst_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2337_; 
v_snd_2241_ = lean_ctor_get(v_a_2214_, 1);
lean_inc(v_snd_2241_);
v_snd_2242_ = lean_ctor_get(v_snd_2241_, 1);
lean_inc(v_snd_2242_);
v_snd_2243_ = lean_ctor_get(v_snd_2242_, 1);
lean_inc(v_snd_2243_);
v_fst_2244_ = lean_ctor_get(v_a_2214_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_a_2214_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v_a_2214_, 1);
lean_dec(v_unused_2338_);
v___x_2246_ = v_a_2214_;
v_isShared_2247_ = v_isSharedCheck_2337_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_fst_2244_);
lean_dec(v_a_2214_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2337_;
goto v_resetjp_2245_;
}
v___jp_2220_:
{
if (lean_obj_tag(v___y_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2232_; 
v_a_2222_ = lean_ctor_get(v___y_2221_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___y_2221_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2224_ = v___y_2221_;
v_isShared_2225_ = v_isSharedCheck_2232_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___y_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2232_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
if (lean_obj_tag(v_a_2222_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; 
lean_dec_ref(v_a_2212_);
v_a_2226_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v_a_2222_, 1);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v_a_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
else
{
lean_object* v_a_2230_; 
lean_del_object(v___x_2224_);
v_a_2230_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v_a_2222_, 1);
v_a_2214_ = v_a_2230_;
goto _start;
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v_a_2212_);
v_a_2233_ = lean_ctor_get(v___y_2221_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___y_2221_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___y_2221_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___y_2221_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
v_resetjp_2245_:
{
lean_object* v_fst_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2335_; 
v_fst_2248_ = lean_ctor_get(v_snd_2241_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_snd_2241_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; 
v_unused_2336_ = lean_ctor_get(v_snd_2241_, 1);
lean_dec(v_unused_2336_);
v___x_2250_ = v_snd_2241_;
v_isShared_2251_ = v_isSharedCheck_2335_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_fst_2248_);
lean_dec(v_snd_2241_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2335_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_fst_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2333_; 
v_fst_2252_ = lean_ctor_get(v_snd_2242_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_snd_2242_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v_snd_2242_, 1);
lean_dec(v_unused_2334_);
v___x_2254_ = v_snd_2242_;
v_isShared_2255_ = v_isSharedCheck_2333_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_fst_2252_);
lean_dec(v_snd_2242_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2333_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_fst_2256_; lean_object* v_snd_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2332_; 
v_fst_2256_ = lean_ctor_get(v_snd_2243_, 0);
v_snd_2257_ = lean_ctor_get(v_snd_2243_, 1);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_snd_2243_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2259_ = v_snd_2243_;
v_isShared_2260_ = v_isSharedCheck_2332_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_snd_2257_);
lean_inc(v_fst_2256_);
lean_dec(v_snd_2243_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2332_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2261_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2));
v___x_2262_ = lean_unsigned_to_nat(3u);
v___x_2263_ = l_Lean_Expr_isAppOfArity(v_fst_2244_, v___x_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2265_; 
lean_dec_ref(v_a_2212_);
if (v_isShared_2260_ == 0)
{
v___x_2265_ = v___x_2259_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_fst_2256_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_snd_2257_);
v___x_2265_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2267_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 1, v___x_2265_);
v___x_2267_ = v___x_2254_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_fst_2252_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2269_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v___x_2267_);
v___x_2269_ = v___x_2250_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_fst_2248_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v___x_2269_);
v___x_2271_ = v___x_2246_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_fst_2244_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2272_; 
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
}
}
}
}
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_del_object(v___x_2259_);
lean_del_object(v___x_2254_);
lean_del_object(v___x_2250_);
lean_del_object(v___x_2246_);
v___x_2277_ = lean_unsigned_to_nat(1u);
v___x_2278_ = l_Lean_Expr_getAppNumArgs(v_fst_2244_);
v___x_2279_ = lean_nat_sub(v___x_2278_, v___x_2277_);
v___x_2280_ = lean_nat_sub(v___x_2279_, v___x_2277_);
lean_dec(v___x_2279_);
v___x_2281_ = l_Lean_Expr_getRevArg_x21(v_fst_2244_, v___x_2280_);
v___x_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
v___x_2283_ = 0;
v___x_2284_ = lean_box(0);
v___x_2285_ = l_Lean_Meta_mkFreshExprMVar(v___x_2282_, v___x_2283_, v___x_2284_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = lean_mk_empty_array_with_capacity(v___x_2277_);
v___x_2288_ = lean_array_push(v___x_2287_, v_a_2286_);
v___x_2289_ = l_Lean_Expr_beta(v_fst_2248_, v___x_2288_);
v___x_2290_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3));
v___x_2291_ = lean_box(0);
v___x_2292_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10);
lean_inc_ref(v_a_2212_);
v___x_2293_ = l_Lean_Meta_simp(v___x_2289_, v_a_2212_, v___x_2290_, v___x_2291_, v___x_2292_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v_fst_2295_; lean_object* v_expr_2296_; lean_object* v___x_2297_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v_fst_2295_ = lean_ctor_get(v_a_2294_, 0);
lean_inc(v_fst_2295_);
lean_dec(v_a_2294_);
v_expr_2296_ = lean_ctor_get(v_fst_2295_, 0);
lean_inc_ref(v_expr_2296_);
lean_dec(v_fst_2295_);
v___x_2297_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2213_, v_expr_2296_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; uint8_t v___x_2303_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = lean_nat_add(v_fst_2252_, v___x_2277_);
lean_dec(v_fst_2252_);
v___x_2303_ = lean_nat_dec_lt(v_a_2298_, v_snd_2257_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = l_Lean_Expr_getAppFn_x27(v_expr_2296_);
v___x_2305_ = l_Lean_Expr_isMVar(v___x_2304_);
lean_dec_ref(v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_dec(v_a_2298_);
v___x_2306_ = lean_box(0);
v___x_2307_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_2278_, v___x_2277_, v_fst_2244_, v___x_2299_, v_expr_2296_, v___x_2306_, v_fst_2256_, v_snd_2257_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v_fst_2244_);
lean_dec(v___x_2278_);
v___y_2221_ = v___x_2307_;
goto v___jp_2220_;
}
else
{
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
goto v___jp_2300_;
}
}
else
{
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
goto v___jp_2300_;
}
v___jp_2300_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = lean_box(0);
lean_inc(v___x_2299_);
v___x_2302_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_2278_, v___x_2277_, v_fst_2244_, v___x_2299_, v_expr_2296_, v___x_2301_, v___x_2299_, v_a_2298_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v_fst_2244_);
lean_dec(v___x_2278_);
v___y_2221_ = v___x_2302_;
goto v___jp_2220_;
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_expr_2296_);
lean_dec(v___x_2278_);
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
lean_dec(v_fst_2252_);
lean_dec(v_fst_2244_);
lean_dec_ref(v_a_2212_);
v_a_2308_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2297_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2297_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v___x_2278_);
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
lean_dec(v_fst_2252_);
lean_dec(v_fst_2244_);
lean_dec_ref(v_a_2212_);
v_a_2316_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2293_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2293_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v___x_2278_);
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
lean_dec(v_fst_2252_);
lean_dec(v_fst_2248_);
lean_dec(v_fst_2244_);
lean_dec_ref(v_a_2212_);
v_a_2324_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2285_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2285_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___boxed(lean_object* v_a_2339_, lean_object* v_xs_2340_, lean_object* v_a_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_2339_, v_xs_2340_, v_a_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v_xs_2340_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(lean_object* v___x_2348_, uint8_t v___x_2349_, lean_object* v_00_u03c3s_2350_, lean_object* v_xs_2351_, lean_object* v_e_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
if (v___x_2349_ == 0)
{
lean_object* v_config_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2432_; 
v_config_2358_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2360_ = v___x_2348_;
v_isShared_2361_ = v_isSharedCheck_2432_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_config_2358_);
lean_dec(v___x_2348_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2432_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
uint8_t v_trackZetaDelta_2362_; lean_object* v_zetaDeltaSet_2363_; lean_object* v_lctx_2364_; lean_object* v_localInstances_2365_; lean_object* v_defEqCtx_x3f_2366_; lean_object* v_synthPendingDepth_2367_; lean_object* v_canUnfold_x3f_2368_; uint8_t v_univApprox_2369_; uint8_t v_inTypeClassResolution_2370_; uint8_t v_cacheInferType_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2430_; 
v_trackZetaDelta_2362_ = lean_ctor_get_uint8(v___y_2353_, sizeof(void*)*7);
v_zetaDeltaSet_2363_ = lean_ctor_get(v___y_2353_, 1);
v_lctx_2364_ = lean_ctor_get(v___y_2353_, 2);
v_localInstances_2365_ = lean_ctor_get(v___y_2353_, 3);
v_defEqCtx_x3f_2366_ = lean_ctor_get(v___y_2353_, 4);
v_synthPendingDepth_2367_ = lean_ctor_get(v___y_2353_, 5);
v_canUnfold_x3f_2368_ = lean_ctor_get(v___y_2353_, 6);
v_univApprox_2369_ = lean_ctor_get_uint8(v___y_2353_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2370_ = lean_ctor_get_uint8(v___y_2353_, sizeof(void*)*7 + 2);
v_cacheInferType_2371_ = lean_ctor_get_uint8(v___y_2353_, sizeof(void*)*7 + 3);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___y_2353_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v___y_2353_, 0);
lean_dec(v_unused_2431_);
v___x_2373_ = v___y_2353_;
v_isShared_2374_ = v_isSharedCheck_2430_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_canUnfold_x3f_2368_);
lean_inc(v_synthPendingDepth_2367_);
lean_inc(v_defEqCtx_x3f_2366_);
lean_inc(v_localInstances_2365_);
lean_inc(v_lctx_2364_);
lean_inc(v_zetaDeltaSet_2363_);
lean_dec(v___y_2353_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2430_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
uint64_t v___x_2375_; lean_object* v___x_2377_; 
v___x_2375_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2358_);
if (v_isShared_2361_ == 0)
{
v___x_2377_ = v___x_2360_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_config_2358_);
v___x_2377_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
lean_ctor_set_uint64(v___x_2377_, sizeof(void*)*1, v___x_2375_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2377_);
v___x_2379_ = v___x_2373_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_zetaDeltaSet_2363_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v_lctx_2364_);
lean_ctor_set(v_reuseFailAlloc_2428_, 3, v_localInstances_2365_);
lean_ctor_set(v_reuseFailAlloc_2428_, 4, v_defEqCtx_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2428_, 5, v_synthPendingDepth_2367_);
lean_ctor_set(v_reuseFailAlloc_2428_, 6, v_canUnfold_x3f_2368_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*7, v_trackZetaDelta_2362_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*7 + 1, v_univApprox_2369_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2370_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*7 + 3, v_cacheInferType_2371_);
v___x_2379_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(v___x_2379_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = l_Lean_Meta_whnfR(v_00_u03c3s_2350_, v___x_2379_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2384_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_2351_, v_e_2352_, v___x_2379_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v___x_2386_ = lean_unsigned_to_nat(0u);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v_a_2385_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_e_2352_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_a_2383_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_2381_, v_xs_2351_, v___x_2390_, v___x_2379_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec_ref(v___x_2379_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2403_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2403_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2403_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_snd_2396_; lean_object* v_snd_2397_; lean_object* v_snd_2398_; lean_object* v_fst_2399_; lean_object* v___x_2401_; 
v_snd_2396_ = lean_ctor_get(v_a_2392_, 1);
lean_inc(v_snd_2396_);
lean_dec(v_a_2392_);
v_snd_2397_ = lean_ctor_get(v_snd_2396_, 1);
lean_inc(v_snd_2397_);
lean_dec(v_snd_2396_);
v_snd_2398_ = lean_ctor_get(v_snd_2397_, 1);
lean_inc(v_snd_2398_);
lean_dec(v_snd_2397_);
v_fst_2399_ = lean_ctor_get(v_snd_2398_, 0);
lean_inc(v_fst_2399_);
lean_dec(v_snd_2398_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v_fst_2399_);
v___x_2401_ = v___x_2394_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_fst_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
v_a_2404_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2391_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2391_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_dec(v_a_2383_);
lean_dec(v_a_2381_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_e_2352_);
return v___x_2384_;
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_a_2381_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_e_2352_);
v_a_2412_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2382_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2382_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_e_2352_);
lean_dec_ref(v_00_u03c3s_2350_);
v_a_2420_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2380_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2380_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
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
lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec_ref(v___y_2353_);
lean_dec_ref(v_e_2352_);
lean_dec_ref(v_00_u03c3s_2350_);
lean_dec_ref(v___x_2348_);
v___x_2433_ = lean_unsigned_to_nat(0u);
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed(lean_object* v___x_2435_, lean_object* v___x_2436_, lean_object* v_00_u03c3s_2437_, lean_object* v_xs_2438_, lean_object* v_e_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
uint8_t v___x_5010__boxed_2445_; lean_object* v_res_2446_; 
v___x_5010__boxed_2445_ = lean_unbox(v___x_2436_);
v_res_2446_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(v___x_2435_, v___x_5010__boxed_2445_, v_00_u03c3s_2437_, v_xs_2438_, v_e_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v_xs_2438_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(lean_object* v_xs_2447_, lean_object* v_00_u03c3s_2448_, lean_object* v_e_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___f_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2455_ = l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig;
v___x_2456_ = lean_array_get_size(v_xs_2447_);
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = lean_nat_dec_eq(v___x_2456_, v___x_2457_);
v___x_2459_ = lean_box(v___x_2458_);
v___f_2460_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2460_, 0, v___x_2455_);
lean_closure_set(v___f_2460_, 1, v___x_2459_);
lean_closure_set(v___f_2460_, 2, v_00_u03c3s_2448_);
lean_closure_set(v___f_2460_, 3, v_xs_2447_);
lean_closure_set(v___f_2460_, 4, v_e_2449_);
v___x_2461_ = 0;
v___x_2462_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_2460_, v___x_2461_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___boxed(lean_object* v_xs_2463_, lean_object* v_00_u03c3s_2464_, lean_object* v_e_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_xs_2463_, v_00_u03c3s_2464_, v_e_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(lean_object* v_a_2472_, lean_object* v_xs_2473_, lean_object* v_inst_2474_, lean_object* v_a_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_2472_, v_xs_2473_, v_a_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___boxed(lean_object* v_a_2482_, lean_object* v_xs_2483_, lean_object* v_inst_2484_, lean_object* v_a_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(v_a_2482_, v_xs_2483_, v_inst_2484_, v_a_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec_ref(v_xs_2483_);
return v_res_2491_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0));
v___x_2494_ = l_Lean_stringToMessageData(v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(lean_object* v_a_2508_, lean_object* v___x_2509_, uint8_t v___x_2510_, lean_object* v___x_2511_, lean_object* v_proof_2512_, lean_object* v_prio_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; lean_object* v_config_2520_; uint8_t v_trackZetaDelta_2521_; lean_object* v_zetaDeltaSet_2522_; lean_object* v_lctx_2523_; lean_object* v_localInstances_2524_; lean_object* v_defEqCtx_x3f_2525_; lean_object* v_synthPendingDepth_2526_; lean_object* v_canUnfold_x3f_2527_; uint8_t v_univApprox_2528_; uint8_t v_inTypeClassResolution_2529_; uint8_t v_cacheInferType_2530_; uint64_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2519_ = l_Lean_Meta_simpGlobalConfig;
v_config_2520_ = lean_ctor_get(v___x_2519_, 0);
v_trackZetaDelta_2521_ = lean_ctor_get_uint8(v___y_2514_, sizeof(void*)*7);
v_zetaDeltaSet_2522_ = lean_ctor_get(v___y_2514_, 1);
v_lctx_2523_ = lean_ctor_get(v___y_2514_, 2);
v_localInstances_2524_ = lean_ctor_get(v___y_2514_, 3);
v_defEqCtx_x3f_2525_ = lean_ctor_get(v___y_2514_, 4);
v_synthPendingDepth_2526_ = lean_ctor_get(v___y_2514_, 5);
v_canUnfold_x3f_2527_ = lean_ctor_get(v___y_2514_, 6);
v_univApprox_2528_ = lean_ctor_get_uint8(v___y_2514_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2529_ = lean_ctor_get_uint8(v___y_2514_, sizeof(void*)*7 + 2);
v_cacheInferType_2530_ = lean_ctor_get_uint8(v___y_2514_, sizeof(void*)*7 + 3);
v___x_2531_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_2520_);
lean_inc_ref(v_config_2520_);
v___x_2532_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2532_, 0, v_config_2520_);
lean_ctor_set_uint64(v___x_2532_, sizeof(void*)*1, v___x_2531_);
lean_inc(v_canUnfold_x3f_2527_);
lean_inc(v_synthPendingDepth_2526_);
lean_inc(v_defEqCtx_x3f_2525_);
lean_inc_ref(v_localInstances_2524_);
lean_inc_ref(v_lctx_2523_);
lean_inc(v_zetaDeltaSet_2522_);
v___x_2533_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v_zetaDeltaSet_2522_);
lean_ctor_set(v___x_2533_, 2, v_lctx_2523_);
lean_ctor_set(v___x_2533_, 3, v_localInstances_2524_);
lean_ctor_set(v___x_2533_, 4, v_defEqCtx_x3f_2525_);
lean_ctor_set(v___x_2533_, 5, v_synthPendingDepth_2526_);
lean_ctor_set(v___x_2533_, 6, v_canUnfold_x3f_2527_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*7, v_trackZetaDelta_2521_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*7 + 1, v_univApprox_2528_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2529_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*7 + 3, v_cacheInferType_2530_);
v___x_2534_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2508_, v___x_2509_, v___x_2510_, v___x_2533_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec_ref_known(v___x_2533_, 7);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v_snd_2536_; lean_object* v_fst_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2638_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
v_snd_2536_ = lean_ctor_get(v_a_2535_, 1);
v_fst_2537_ = lean_ctor_get(v_a_2535_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_a_2535_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2539_ = v_a_2535_;
v_isShared_2540_ = v_isSharedCheck_2638_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_snd_2536_);
lean_inc(v_fst_2537_);
lean_dec(v_a_2535_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2638_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v_snd_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2636_; 
v_snd_2541_ = lean_ctor_get(v_snd_2536_, 1);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_snd_2536_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v_snd_2536_, 0);
lean_dec(v_unused_2637_);
v___x_2543_ = v_snd_2536_;
v_isShared_2544_ = v_isSharedCheck_2636_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_snd_2541_);
lean_dec(v_snd_2536_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2636_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_Meta_whnfR(v_snd_2541_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc_n(v_a_2546_, 2);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2558_ = l_Lean_Expr_cleanupAnnotations(v_a_2546_);
v___x_2559_ = l_Lean_Expr_isApp(v___x_2558_);
if (v___x_2559_ == 0)
{
lean_dec_ref(v___x_2558_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v___y_2548_ = v___y_2514_;
v___y_2549_ = v___y_2515_;
v___y_2550_ = v___y_2516_;
v___y_2551_ = v___y_2517_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2560_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2558_);
v___x_2561_ = l_Lean_Expr_isApp(v___x_2560_);
if (v___x_2561_ == 0)
{
lean_dec_ref(v___x_2560_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v___y_2548_ = v___y_2514_;
v___y_2549_ = v___y_2515_;
v___y_2550_ = v___y_2516_;
v___y_2551_ = v___y_2517_;
goto v___jp_2547_;
}
else
{
lean_object* v_arg_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v_arg_2562_ = lean_ctor_get(v___x_2560_, 1);
lean_inc_ref(v_arg_2562_);
v___x_2563_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2560_);
v___x_2564_ = l_Lean_Expr_isApp(v___x_2563_);
if (v___x_2564_ == 0)
{
lean_dec_ref(v___x_2563_);
lean_dec_ref(v_arg_2562_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v___y_2548_ = v___y_2514_;
v___y_2549_ = v___y_2515_;
v___y_2550_ = v___y_2516_;
v___y_2551_ = v___y_2517_;
goto v___jp_2547_;
}
else
{
lean_object* v_arg_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v_arg_2565_ = lean_ctor_get(v___x_2563_, 1);
lean_inc_ref(v_arg_2565_);
v___x_2566_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2563_);
v___x_2567_ = l_Lean_Expr_isApp(v___x_2566_);
if (v___x_2567_ == 0)
{
lean_dec_ref(v___x_2566_);
lean_dec_ref(v_arg_2565_);
lean_dec_ref(v_arg_2562_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v___y_2548_ = v___y_2514_;
v___y_2549_ = v___y_2515_;
v___y_2550_ = v___y_2516_;
v___y_2551_ = v___y_2517_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2566_);
v___x_2569_ = l_Lean_Expr_isApp(v___x_2568_);
if (v___x_2569_ == 0)
{
lean_dec_ref(v___x_2568_);
lean_dec_ref(v_arg_2565_);
lean_dec_ref(v_arg_2562_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v___y_2548_ = v___y_2514_;
v___y_2549_ = v___y_2515_;
v___y_2550_ = v___y_2516_;
v___y_2551_ = v___y_2517_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2570_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2568_);
v___x_2571_ = l_Lean_Expr_isApp(v___x_2570_);
if (v___x_2571_ == 0)
{
lean_dec_ref(v___x_2570_);
lean_dec_ref(v_arg_2565_);
lean_dec_ref(v_arg_2562_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v___y_2548_ = v___y_2514_;
v___y_2549_ = v___y_2515_;
v___y_2550_ = v___y_2516_;
v___y_2551_ = v___y_2517_;
goto v___jp_2547_;
}
else
{
lean_object* v_arg_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
v_arg_2572_ = lean_ctor_get(v___x_2570_, 1);
lean_inc_ref(v_arg_2572_);
v___x_2573_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2570_);
v___x_2574_ = l_Lean_Expr_isApp(v___x_2573_);
if (v___x_2574_ == 0)
{
lean_dec_ref(v___x_2573_);
lean_dec_ref(v_arg_2572_);
lean_dec_ref(v_arg_2565_);
lean_dec_ref(v_arg_2562_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v___y_2548_ = v___y_2514_;
v___y_2549_ = v___y_2515_;
v___y_2550_ = v___y_2516_;
v___y_2551_ = v___y_2517_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2575_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2573_);
v___x_2576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4));
v___x_2577_ = l_Lean_Expr_isConstOf(v___x_2575_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_dec_ref(v___x_2575_);
lean_dec_ref(v_arg_2572_);
lean_dec_ref(v_arg_2565_);
lean_dec_ref(v_arg_2562_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v___y_2548_ = v___y_2514_;
v___y_2549_ = v___y_2515_;
v___y_2550_ = v___y_2516_;
v___y_2551_ = v___y_2517_;
goto v___jp_2547_;
}
else
{
uint8_t v___x_2578_; lean_object* v___x_2579_; 
lean_dec(v_a_2546_);
lean_del_object(v___x_2543_);
v___x_2578_ = 0;
lean_inc_ref(v_arg_2565_);
v___x_2579_ = l_Lean_Meta_DiscrTree_mkPath(v_arg_2565_, v___x_2578_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7));
v___x_2582_ = l_Lean_Expr_constLevels_x21(v___x_2575_);
lean_dec_ref(v___x_2575_);
v___x_2583_ = lean_unsigned_to_nat(0u);
v___x_2584_ = l_List_get_x21Internal___redArg(v___x_2511_, v___x_2582_, v___x_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
if (v_isShared_2540_ == 0)
{
lean_ctor_set_tag(v___x_2539_, 1);
lean_ctor_set(v___x_2539_, 1, v___x_2585_);
lean_ctor_set(v___x_2539_, 0, v___x_2584_);
v___x_2587_ = v___x_2539_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = l_Lean_mkConst(v___x_2581_, v___x_2587_);
v___x_2589_ = l_Lean_Expr_app___override(v___x_2588_, v_arg_2572_);
lean_inc(v_fst_2537_);
v___x_2590_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_fst_2537_, v___x_2589_, v_arg_2562_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; uint8_t v___x_2592_; lean_object* v___x_2593_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2592_ = 1;
v___x_2593_ = l_Lean_Meta_mkForallFVars(v_fst_2537_, v_arg_2565_, v___x_2578_, v___x_2577_, v___x_2577_, v___x_2592_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v_fst_2537_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2602_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2598_, 0, v_a_2580_);
lean_ctor_set(v___x_2598_, 1, v_a_2594_);
lean_ctor_set(v___x_2598_, 2, v_proof_2512_);
lean_ctor_set(v___x_2598_, 3, v_a_2591_);
lean_ctor_set(v___x_2598_, 4, v_prio_2513_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2598_);
v___x_2600_ = v___x_2596_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec(v_a_2591_);
lean_dec(v_a_2580_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v_a_2603_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2593_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2593_);
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
lean_dec(v_a_2580_);
lean_dec_ref(v_arg_2565_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v_a_2611_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2590_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2590_);
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
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v___x_2575_);
lean_dec_ref(v_arg_2572_);
lean_dec_ref(v_arg_2565_);
lean_dec_ref(v_arg_2562_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v_a_2620_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2579_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2579_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
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
v___jp_2547_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2552_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1);
v___x_2553_ = l_Lean_indentExpr(v_a_2546_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 7);
lean_ctor_set(v___x_2543_, 1, v___x_2553_);
lean_ctor_set(v___x_2543_, 0, v___x_2552_);
v___x_2555_ = v___x_2543_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2555_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
return v___x_2556_;
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_del_object(v___x_2543_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v_a_2628_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2545_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2545_);
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
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v_prio_2513_);
lean_dec_ref(v_proof_2512_);
v_a_2639_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2534_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2534_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed(lean_object* v_a_2647_, lean_object* v___x_2648_, lean_object* v___x_2649_, lean_object* v___x_2650_, lean_object* v_proof_2651_, lean_object* v_prio_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
uint8_t v___x_3664__boxed_2658_; lean_object* v_res_2659_; 
v___x_3664__boxed_2658_ = lean_unbox(v___x_2649_);
v_res_2659_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(v_a_2647_, v___x_2648_, v___x_3664__boxed_2658_, v___x_2650_, v_proof_2651_, v_prio_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___x_2650_);
return v_res_2659_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0));
v___x_2662_ = l_Lean_stringToMessageData(v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(lean_object* v_type_2663_, lean_object* v_proof_2664_, lean_object* v_prio_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2671_; lean_object* v_a_2672_; lean_object* v___x_2673_; 
v___x_2671_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_type_2663_, v_a_2667_);
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc_n(v_a_2672_, 2);
lean_dec_ref(v___x_2671_);
v___x_2673_ = l_Lean_Meta_isProp(v_a_2672_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; uint8_t v___x_2687_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = lean_box(0);
v___x_2687_ = lean_unbox(v_a_2674_);
lean_dec(v_a_2674_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_prio_2665_);
lean_dec_ref(v_proof_2664_);
v___x_2688_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1, &l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1);
v___x_2689_ = l_Lean_indentExpr(v_a_2672_);
v___x_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2688_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2690_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2691_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2691_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
v___y_2677_ = v_a_2666_;
v___y_2678_ = v_a_2667_;
v___y_2679_ = v_a_2668_;
v___y_2680_ = v_a_2669_;
goto v___jp_2676_;
}
v___jp_2676_:
{
lean_object* v___x_2681_; uint8_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___f_2684_; uint8_t v___x_2685_; lean_object* v___x_2686_; 
v___x_2681_ = lean_box(0);
v___x_2682_ = 0;
v___x_2683_ = lean_box(v___x_2682_);
v___f_2684_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2684_, 0, v_a_2672_);
lean_closure_set(v___f_2684_, 1, v___x_2681_);
lean_closure_set(v___f_2684_, 2, v___x_2683_);
lean_closure_set(v___f_2684_, 3, v___x_2675_);
lean_closure_set(v___f_2684_, 4, v_proof_2664_);
lean_closure_set(v___f_2684_, 5, v_prio_2665_);
v___x_2685_ = 0;
v___x_2686_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_2684_, v___x_2685_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
return v___x_2686_;
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_a_2672_);
lean_dec(v_prio_2665_);
lean_dec_ref(v_proof_2664_);
v_a_2700_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2673_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2673_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___boxed(lean_object* v_type_2708_, lean_object* v_proof_2709_, lean_object* v_prio_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_type_2708_, v_proof_2709_, v_prio_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(lean_object* v_declName_2717_, lean_object* v_prio_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v___x_2724_; 
lean_inc(v_declName_2717_);
v___x_2724_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_2717_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
v___x_2726_ = l_Lean_ConstantInfo_levelParams(v_a_2725_);
lean_dec(v_a_2725_);
v___x_2727_ = lean_box(0);
v___x_2728_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_2726_, v___x_2727_);
lean_inc(v_declName_2717_);
v___x_2729_ = l_Lean_mkConst(v_declName_2717_, v___x_2728_);
lean_inc(v_a_2722_);
lean_inc_ref(v_a_2721_);
lean_inc(v_a_2720_);
lean_inc_ref(v_a_2719_);
v___x_2730_ = lean_infer_type(v___x_2729_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_declName_2717_);
v___x_2733_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_2731_, v___x_2732_, v_prio_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
return v___x_2733_;
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_prio_2718_);
lean_dec(v_declName_2717_);
v_a_2734_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2730_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2730_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
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
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_prio_2718_);
lean_dec(v_declName_2717_);
v_a_2742_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2724_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2724_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst___boxed(lean_object* v_declName_2750_, lean_object* v_prio_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_2750_, v_prio_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2757_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(lean_object* v_fvar_2764_, lean_object* v_prio_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v___x_2771_; 
lean_inc(v_fvar_2764_);
v___x_2771_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvar_2764_, v_a_2766_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
if (lean_obj_tag(v_a_2772_) == 1)
{
lean_object* v_val_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2782_; 
v_val_2773_ = lean_ctor_get(v_a_2772_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_a_2772_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2775_ = v_a_2772_;
v_isShared_2776_ = v_isSharedCheck_2782_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_val_2773_);
lean_dec(v_a_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2782_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2777_ = l_Lean_LocalDecl_type(v_val_2773_);
lean_dec(v_val_2773_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v_fvar_2764_);
v___x_2779_ = v___x_2775_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_fvar_2764_);
v___x_2779_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; 
v___x_2780_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v___x_2777_, v___x_2779_, v_prio_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
return v___x_2780_;
}
}
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_dec(v_a_2772_);
lean_dec(v_prio_2765_);
v___x_2783_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1);
v___x_2784_ = l_Lean_MessageData_ofName(v_fvar_2764_);
v___x_2785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3);
v___x_2787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2785_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_2787_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
return v___x_2788_;
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v_prio_2765_);
lean_dec(v_fvar_2764_);
v_a_2789_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2771_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2771_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___boxed(lean_object* v_fvar_2797_, lean_object* v_prio_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvar_2797_, v_prio_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(lean_object* v___y_2805_){
_start:
{
lean_object* v___x_2807_; lean_object* v_ngen_2808_; lean_object* v_namePrefix_2809_; lean_object* v_idx_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2839_; 
v___x_2807_ = lean_st_ref_get(v___y_2805_);
v_ngen_2808_ = lean_ctor_get(v___x_2807_, 2);
lean_inc_ref(v_ngen_2808_);
lean_dec(v___x_2807_);
v_namePrefix_2809_ = lean_ctor_get(v_ngen_2808_, 0);
v_idx_2810_ = lean_ctor_get(v_ngen_2808_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_ngen_2808_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2812_ = v_ngen_2808_;
v_isShared_2813_ = v_isSharedCheck_2839_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_idx_2810_);
lean_inc(v_namePrefix_2809_);
lean_dec(v_ngen_2808_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2839_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v_env_2815_; lean_object* v_nextMacroScope_2816_; lean_object* v_auxDeclNGen_2817_; lean_object* v_traceState_2818_; lean_object* v_cache_2819_; lean_object* v_messages_2820_; lean_object* v_infoState_2821_; lean_object* v_snapshotTasks_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2837_; 
v___x_2814_ = lean_st_ref_take(v___y_2805_);
v_env_2815_ = lean_ctor_get(v___x_2814_, 0);
v_nextMacroScope_2816_ = lean_ctor_get(v___x_2814_, 1);
v_auxDeclNGen_2817_ = lean_ctor_get(v___x_2814_, 3);
v_traceState_2818_ = lean_ctor_get(v___x_2814_, 4);
v_cache_2819_ = lean_ctor_get(v___x_2814_, 5);
v_messages_2820_ = lean_ctor_get(v___x_2814_, 6);
v_infoState_2821_ = lean_ctor_get(v___x_2814_, 7);
v_snapshotTasks_2822_ = lean_ctor_get(v___x_2814_, 8);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; 
v_unused_2838_ = lean_ctor_get(v___x_2814_, 2);
lean_dec(v_unused_2838_);
v___x_2824_ = v___x_2814_;
v_isShared_2825_ = v_isSharedCheck_2837_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_snapshotTasks_2822_);
lean_inc(v_infoState_2821_);
lean_inc(v_messages_2820_);
lean_inc(v_cache_2819_);
lean_inc(v_traceState_2818_);
lean_inc(v_auxDeclNGen_2817_);
lean_inc(v_nextMacroScope_2816_);
lean_inc(v_env_2815_);
lean_dec(v___x_2814_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2837_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v_r_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
lean_inc(v_idx_2810_);
lean_inc(v_namePrefix_2809_);
v_r_2826_ = l_Lean_Name_num___override(v_namePrefix_2809_, v_idx_2810_);
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_add(v_idx_2810_, v___x_2827_);
lean_dec(v_idx_2810_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 1, v___x_2828_);
v___x_2830_ = v___x_2812_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_namePrefix_2809_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2832_; 
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 2, v___x_2830_);
v___x_2832_ = v___x_2824_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_env_2815_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_nextMacroScope_2816_);
lean_ctor_set(v_reuseFailAlloc_2835_, 2, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2835_, 3, v_auxDeclNGen_2817_);
lean_ctor_set(v_reuseFailAlloc_2835_, 4, v_traceState_2818_);
lean_ctor_set(v_reuseFailAlloc_2835_, 5, v_cache_2819_);
lean_ctor_set(v_reuseFailAlloc_2835_, 6, v_messages_2820_);
lean_ctor_set(v_reuseFailAlloc_2835_, 7, v_infoState_2821_);
lean_ctor_set(v_reuseFailAlloc_2835_, 8, v_snapshotTasks_2822_);
v___x_2832_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_st_ref_set(v___y_2805_, v___x_2832_);
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_r_2826_);
return v___x_2834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg___boxed(lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_2840_);
lean_dec(v___y_2840_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_2846_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___boxed(lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(lean_object* v_ref_2855_, lean_object* v_proof_2856_, lean_object* v_prio_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v___x_2863_; 
lean_inc(v_a_2861_);
lean_inc_ref(v_a_2860_);
lean_inc(v_a_2859_);
lean_inc_ref(v_a_2858_);
lean_inc_ref(v_proof_2856_);
v___x_2863_ = lean_infer_type(v_proof_2856_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; lean_object* v_a_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v___x_2865_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v_a_2861_);
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref(v___x_2865_);
v___x_2867_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2867_, 0, v_a_2866_);
lean_ctor_set(v___x_2867_, 1, v_ref_2855_);
lean_ctor_set(v___x_2867_, 2, v_proof_2856_);
v___x_2868_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_2864_, v___x_2867_, v_prio_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
return v___x_2868_;
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec(v_prio_2857_);
lean_dec_ref(v_proof_2856_);
lean_dec(v_ref_2855_);
v_a_2869_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2863_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2863_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx___boxed(lean_object* v_ref_2877_, lean_object* v_proof_2878_, lean_object* v_prio_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(v_ref_2877_, v_proof_2878_, v_prio_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
return v_res_2885_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2886_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
return v___x_2888_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
v___x_2892_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
lean_ctor_set(v___x_2892_, 2, v___x_2891_);
lean_ctor_set(v___x_2892_, 3, v___x_2891_);
lean_ctor_set(v___x_2892_, 4, v___x_2891_);
lean_ctor_set(v___x_2892_, 5, v___x_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(lean_object* v_ext_2893_, lean_object* v_b_2894_, uint8_t v_kind_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_currNamespace_2900_; lean_object* v___x_2901_; lean_object* v_env_2902_; lean_object* v_nextMacroScope_2903_; lean_object* v_ngen_2904_; lean_object* v_auxDeclNGen_2905_; lean_object* v_traceState_2906_; lean_object* v_messages_2907_; lean_object* v_infoState_2908_; lean_object* v_snapshotTasks_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2936_; 
v_currNamespace_2900_ = lean_ctor_get(v___y_2897_, 6);
v___x_2901_ = lean_st_ref_take(v___y_2898_);
v_env_2902_ = lean_ctor_get(v___x_2901_, 0);
v_nextMacroScope_2903_ = lean_ctor_get(v___x_2901_, 1);
v_ngen_2904_ = lean_ctor_get(v___x_2901_, 2);
v_auxDeclNGen_2905_ = lean_ctor_get(v___x_2901_, 3);
v_traceState_2906_ = lean_ctor_get(v___x_2901_, 4);
v_messages_2907_ = lean_ctor_get(v___x_2901_, 6);
v_infoState_2908_ = lean_ctor_get(v___x_2901_, 7);
v_snapshotTasks_2909_ = lean_ctor_get(v___x_2901_, 8);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2936_ == 0)
{
lean_object* v_unused_2937_; 
v_unused_2937_ = lean_ctor_get(v___x_2901_, 5);
lean_dec(v_unused_2937_);
v___x_2911_ = v___x_2901_;
v_isShared_2912_ = v_isSharedCheck_2936_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_snapshotTasks_2909_);
lean_inc(v_infoState_2908_);
lean_inc(v_messages_2907_);
lean_inc(v_traceState_2906_);
lean_inc(v_auxDeclNGen_2905_);
lean_inc(v_ngen_2904_);
lean_inc(v_nextMacroScope_2903_);
lean_inc(v_env_2902_);
lean_dec(v___x_2901_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2936_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
lean_inc(v_currNamespace_2900_);
v___x_2913_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2902_, v_ext_2893_, v_b_2894_, v_kind_2895_, v_currNamespace_2900_);
v___x_2914_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 5, v___x_2914_);
lean_ctor_set(v___x_2911_, 0, v___x_2913_);
v___x_2916_ = v___x_2911_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_nextMacroScope_2903_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v_ngen_2904_);
lean_ctor_set(v_reuseFailAlloc_2935_, 3, v_auxDeclNGen_2905_);
lean_ctor_set(v_reuseFailAlloc_2935_, 4, v_traceState_2906_);
lean_ctor_set(v_reuseFailAlloc_2935_, 5, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2935_, 6, v_messages_2907_);
lean_ctor_set(v_reuseFailAlloc_2935_, 7, v_infoState_2908_);
lean_ctor_set(v_reuseFailAlloc_2935_, 8, v_snapshotTasks_2909_);
v___x_2916_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v_mctx_2919_; lean_object* v_zetaDeltaFVarIds_2920_; lean_object* v_postponed_2921_; lean_object* v_diag_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2933_; 
v___x_2917_ = lean_st_ref_set(v___y_2898_, v___x_2916_);
v___x_2918_ = lean_st_ref_take(v___y_2896_);
v_mctx_2919_ = lean_ctor_get(v___x_2918_, 0);
v_zetaDeltaFVarIds_2920_ = lean_ctor_get(v___x_2918_, 2);
v_postponed_2921_ = lean_ctor_get(v___x_2918_, 3);
v_diag_2922_ = lean_ctor_get(v___x_2918_, 4);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; 
v_unused_2934_ = lean_ctor_get(v___x_2918_, 1);
lean_dec(v_unused_2934_);
v___x_2924_ = v___x_2918_;
v_isShared_2925_ = v_isSharedCheck_2933_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_diag_2922_);
lean_inc(v_postponed_2921_);
lean_inc(v_zetaDeltaFVarIds_2920_);
lean_inc(v_mctx_2919_);
lean_dec(v___x_2918_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2933_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 1, v___x_2926_);
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_mctx_2919_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2932_, 2, v_zetaDeltaFVarIds_2920_);
lean_ctor_set(v_reuseFailAlloc_2932_, 3, v_postponed_2921_);
lean_ctor_set(v_reuseFailAlloc_2932_, 4, v_diag_2922_);
v___x_2928_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_st_ref_set(v___y_2896_, v___x_2928_);
v___x_2930_ = lean_box(0);
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___boxed(lean_object* v_ext_2938_, lean_object* v_b_2939_, lean_object* v_kind_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
uint8_t v_kind_boxed_2945_; lean_object* v_res_2946_; 
v_kind_boxed_2945_ = lean_unbox(v_kind_2940_);
v_res_2946_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2938_, v_b_2939_, v_kind_boxed_2945_, v___y_2941_, v___y_2942_, v___y_2943_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(lean_object* v_00_u03b1_2947_, lean_object* v_00_u03b2_2948_, lean_object* v_00_u03c3_2949_, lean_object* v_ext_2950_, lean_object* v_b_2951_, uint8_t v_kind_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2950_, v_b_2951_, v_kind_2952_, v___y_2954_, v___y_2955_, v___y_2956_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___boxed(lean_object* v_00_u03b1_2959_, lean_object* v_00_u03b2_2960_, lean_object* v_00_u03c3_2961_, lean_object* v_ext_2962_, lean_object* v_b_2963_, lean_object* v_kind_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
uint8_t v_kind_boxed_2970_; lean_object* v_res_2971_; 
v_kind_boxed_2970_ = lean_unbox(v_kind_2964_);
v_res_2971_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(v_00_u03b1_2959_, v_00_u03b2_2960_, v_00_u03c3_2961_, v_ext_2962_, v_b_2963_, v_kind_boxed_2970_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(lean_object* v_ext_2972_, lean_object* v_declName_2973_, lean_object* v_prio_2974_, uint8_t v_attrKind_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_2973_, v_prio_2974_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2983_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref_known(v___x_2981_, 1);
v___x_2983_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_2972_, v_a_2982_, v_attrKind_2975_, v_a_2977_, v_a_2978_, v_a_2979_);
return v___x_2983_;
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v_ext_2972_);
v_a_2984_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2981_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2981_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst___boxed(lean_object* v_ext_2992_, lean_object* v_declName_2993_, lean_object* v_prio_2994_, lean_object* v_attrKind_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
uint8_t v_attrKind_boxed_3001_; lean_object* v_res_3002_; 
v_attrKind_boxed_3001_ = lean_unbox(v_attrKind_2995_);
v_res_3002_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(v_ext_2992_, v_declName_2993_, v_prio_2994_, v_attrKind_boxed_3001_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
lean_dec(v_a_2999_);
lean_dec_ref(v_a_2998_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(lean_object* v_ext_3003_, lean_object* v_fvar_3004_, lean_object* v_prio_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvar_3004_, v_prio_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; uint8_t v___x_3013_; lean_object* v___x_3014_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = 1;
v___x_3014_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_3003_, v_a_3012_, v___x_3013_, v_a_3007_, v_a_3008_, v_a_3009_);
return v___x_3014_;
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v_ext_3003_);
v_a_3015_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3011_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3011_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal___boxed(lean_object* v_ext_3023_, lean_object* v_fvar_3024_, lean_object* v_prio_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(v_ext_3023_, v_fvar_3024_, v_prio_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(lean_object* v_x_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3034_, 0, v_a_3033_);
lean_inc_ref_n(v___x_3034_, 2);
v___x_3035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
lean_ctor_set(v___x_3035_, 2, v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed(lean_object* v_x_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(v_x_3036_, v_a_3037_);
lean_dec_ref(v_x_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(lean_object* v___y_3039_){
_start:
{
lean_inc_ref(v___y_3039_);
return v___y_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed(lean_object* v___y_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(v___y_3040_);
lean_dec_ref(v___y_3040_);
return v_res_3041_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5(void){
_start:
{
lean_object* v___f_3048_; lean_object* v___f_3049_; lean_object* v___x_3050_; lean_object* v___f_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___f_3048_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1));
v___f_3049_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2));
v___x_3050_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2);
v___f_3051_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0));
v___x_3052_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4));
v___x_3053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v___f_3051_);
lean_ctor_set(v___x_3053_, 2, v___x_3050_);
lean_ctor_set(v___x_3053_, 3, v___f_3049_);
lean_ctor_set(v___x_3053_, 4, v___f_3048_);
return v___x_3053_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt(void){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt;
v___x_3057_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2____boxed(lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(lean_object* v_ext_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v___x_3063_; lean_object* v_ext_3064_; lean_object* v_toEnvExtension_3065_; lean_object* v_env_3066_; lean_object* v_asyncMode_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3063_ = lean_st_ref_get(v_a_3061_);
v_ext_3064_ = lean_ctor_get(v_ext_3060_, 1);
v_toEnvExtension_3065_ = lean_ctor_get(v_ext_3064_, 0);
v_env_3066_ = lean_ctor_get(v___x_3063_, 0);
lean_inc_ref(v_env_3066_);
lean_dec(v___x_3063_);
v_asyncMode_3067_ = lean_ctor_get(v_toEnvExtension_3065_, 2);
v___x_3068_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
v___x_3069_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3068_, v_ext_3060_, v_env_3066_, v_asyncMode_3067_);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg___boxed(lean_object* v_ext_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_3071_, v_a_3072_);
lean_dec(v_a_3072_);
lean_dec_ref(v_ext_3071_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(lean_object* v_ext_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_3075_, v_a_3077_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___boxed(lean_object* v_ext_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(v_ext_3080_, v_a_3081_, v_a_3082_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
lean_dec_ref(v_ext_3080_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(lean_object* v_a_3085_){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
v___x_3088_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v___x_3087_, v_a_3085_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg___boxed(lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3089_);
lean_dec(v_a_3089_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3093_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___boxed(lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(v_a_3096_, v_a_3097_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorIdx(lean_object* v_x_3100_){
_start:
{
if (lean_obj_tag(v_x_3100_) == 0)
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_unsigned_to_nat(0u);
return v___x_3101_;
}
else
{
lean_object* v___x_3102_; 
v___x_3102_ = lean_unsigned_to_nat(1u);
return v___x_3102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorIdx___boxed(lean_object* v_x_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorIdx(v_x_3103_);
lean_dec(v_x_3103_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim___redArg(lean_object* v_t_3105_, lean_object* v_k_3106_){
_start:
{
if (lean_obj_tag(v_t_3105_) == 0)
{
return v_k_3106_;
}
else
{
lean_object* v_etaArgs_3107_; lean_object* v___x_3108_; 
v_etaArgs_3107_ = lean_ctor_get(v_t_3105_, 0);
lean_inc(v_etaArgs_3107_);
lean_dec_ref_known(v_t_3105_, 1);
v___x_3108_ = lean_apply_1(v_k_3106_, v_etaArgs_3107_);
return v___x_3108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim(lean_object* v_motive_3109_, lean_object* v_ctorIdx_3110_, lean_object* v_t_3111_, lean_object* v_h_3112_, lean_object* v_k_3113_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_3111_, v_k_3113_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim___boxed(lean_object* v_motive_3115_, lean_object* v_ctorIdx_3116_, lean_object* v_t_3117_, lean_object* v_h_3118_, lean_object* v_k_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim(v_motive_3115_, v_ctorIdx_3116_, v_t_3117_, v_h_3118_, v_k_3119_);
lean_dec(v_ctorIdx_3116_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_triple_elim___redArg(lean_object* v_t_3121_, lean_object* v_triple_3122_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_3121_, v_triple_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_triple_elim(lean_object* v_motive_3124_, lean_object* v_t_3125_, lean_object* v_h_3126_, lean_object* v_triple_3127_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_3125_, v_triple_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_simp_elim___redArg(lean_object* v_t_3129_, lean_object* v_simp_3130_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_3129_, v_simp_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_simp_elim(lean_object* v_motive_3132_, lean_object* v_t_3133_, lean_object* v_h_3134_, lean_object* v_simp_3135_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_3133_, v_simp_3135_);
return v___x_3136_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheoremKind_default(void){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = lean_box(0);
return v___x_3137_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheoremKind(void){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_box(0);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorIdx(lean_object* v_x_3139_){
_start:
{
switch(lean_obj_tag(v_x_3139_))
{
case 0:
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_unsigned_to_nat(0u);
return v___x_3140_;
}
case 1:
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_unsigned_to_nat(1u);
return v___x_3141_;
}
default: 
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_unsigned_to_nat(2u);
return v___x_3142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorIdx___boxed(lean_object* v_x_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorIdx(v_x_3143_);
lean_dec_ref(v_x_3143_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___redArg(lean_object* v_t_3145_, lean_object* v_k_3146_){
_start:
{
if (lean_obj_tag(v_t_3145_) == 2)
{
lean_object* v_id_3147_; lean_object* v_ref_3148_; lean_object* v_proof_3149_; lean_object* v___x_3150_; 
v_id_3147_ = lean_ctor_get(v_t_3145_, 0);
lean_inc(v_id_3147_);
v_ref_3148_ = lean_ctor_get(v_t_3145_, 1);
lean_inc(v_ref_3148_);
v_proof_3149_ = lean_ctor_get(v_t_3145_, 2);
lean_inc_ref(v_proof_3149_);
lean_dec_ref_known(v_t_3145_, 3);
v___x_3150_ = lean_apply_3(v_k_3146_, v_id_3147_, v_ref_3148_, v_proof_3149_);
return v___x_3150_;
}
else
{
lean_object* v_declName_3151_; lean_object* v___x_3152_; 
v_declName_3151_ = lean_ctor_get(v_t_3145_, 0);
lean_inc(v_declName_3151_);
lean_dec_ref(v_t_3145_);
v___x_3152_ = lean_apply_1(v_k_3146_, v_declName_3151_);
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim(lean_object* v_motive_3153_, lean_object* v_ctorIdx_3154_, lean_object* v_t_3155_, lean_object* v_h_3156_, lean_object* v_k_3157_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___redArg(v_t_3155_, v_k_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___boxed(lean_object* v_motive_3159_, lean_object* v_ctorIdx_3160_, lean_object* v_t_3161_, lean_object* v_h_3162_, lean_object* v_k_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim(v_motive_3159_, v_ctorIdx_3160_, v_t_3161_, v_h_3162_, v_k_3163_);
lean_dec(v_ctorIdx_3160_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_global_elim___redArg(lean_object* v_t_3165_, lean_object* v_global_3166_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___redArg(v_t_3165_, v_global_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_global_elim(lean_object* v_motive_3168_, lean_object* v_t_3169_, lean_object* v_h_3170_, lean_object* v_global_3171_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___redArg(v_t_3169_, v_global_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_local_elim___redArg(lean_object* v_t_3173_, lean_object* v_local_3174_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___redArg(v_t_3173_, v_local_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_local_elim(lean_object* v_motive_3176_, lean_object* v_t_3177_, lean_object* v_h_3178_, lean_object* v_local_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___redArg(v_t_3177_, v_local_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_stx_elim___redArg(lean_object* v_t_3181_, lean_object* v_stx_3182_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___redArg(v_t_3181_, v_stx_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_stx_elim(lean_object* v_motive_3184_, lean_object* v_t_3185_, lean_object* v_h_3186_, lean_object* v_stx_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ctorElim___redArg(v_t_3185_, v_stx_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq(lean_object* v_x_3193_, lean_object* v_x_3194_){
_start:
{
switch(lean_obj_tag(v_x_3193_))
{
case 0:
{
if (lean_obj_tag(v_x_3194_) == 0)
{
lean_object* v_declName_3195_; lean_object* v_declName_3196_; uint8_t v___x_3197_; 
v_declName_3195_ = lean_ctor_get(v_x_3193_, 0);
lean_inc(v_declName_3195_);
lean_dec_ref_known(v_x_3193_, 1);
v_declName_3196_ = lean_ctor_get(v_x_3194_, 0);
lean_inc(v_declName_3196_);
lean_dec_ref_known(v_x_3194_, 1);
v___x_3197_ = lean_name_eq(v_declName_3195_, v_declName_3196_);
lean_dec(v_declName_3196_);
lean_dec(v_declName_3195_);
return v___x_3197_;
}
else
{
uint8_t v___x_3198_; 
lean_dec_ref_known(v_x_3193_, 1);
lean_dec_ref(v_x_3194_);
v___x_3198_ = 0;
return v___x_3198_;
}
}
case 1:
{
if (lean_obj_tag(v_x_3194_) == 1)
{
lean_object* v_fvarId_3199_; lean_object* v_fvarId_3200_; uint8_t v___x_3201_; 
v_fvarId_3199_ = lean_ctor_get(v_x_3193_, 0);
lean_inc(v_fvarId_3199_);
lean_dec_ref_known(v_x_3193_, 1);
v_fvarId_3200_ = lean_ctor_get(v_x_3194_, 0);
lean_inc(v_fvarId_3200_);
lean_dec_ref_known(v_x_3194_, 1);
v___x_3201_ = l_Lean_instBEqFVarId_beq(v_fvarId_3199_, v_fvarId_3200_);
lean_dec(v_fvarId_3200_);
lean_dec(v_fvarId_3199_);
return v___x_3201_;
}
else
{
uint8_t v___x_3202_; 
lean_dec_ref_known(v_x_3193_, 1);
lean_dec_ref(v_x_3194_);
v___x_3202_ = 0;
return v___x_3202_;
}
}
default: 
{
if (lean_obj_tag(v_x_3194_) == 2)
{
lean_object* v_id_3203_; lean_object* v_ref_3204_; lean_object* v_proof_3205_; lean_object* v_id_3206_; lean_object* v_ref_3207_; lean_object* v_proof_3208_; uint8_t v___x_3209_; 
v_id_3203_ = lean_ctor_get(v_x_3193_, 0);
lean_inc(v_id_3203_);
v_ref_3204_ = lean_ctor_get(v_x_3193_, 1);
lean_inc(v_ref_3204_);
v_proof_3205_ = lean_ctor_get(v_x_3193_, 2);
lean_inc_ref(v_proof_3205_);
lean_dec_ref_known(v_x_3193_, 3);
v_id_3206_ = lean_ctor_get(v_x_3194_, 0);
lean_inc(v_id_3206_);
v_ref_3207_ = lean_ctor_get(v_x_3194_, 1);
lean_inc(v_ref_3207_);
v_proof_3208_ = lean_ctor_get(v_x_3194_, 2);
lean_inc_ref(v_proof_3208_);
lean_dec_ref_known(v_x_3194_, 3);
v___x_3209_ = lean_name_eq(v_id_3203_, v_id_3206_);
lean_dec(v_id_3206_);
lean_dec(v_id_3203_);
if (v___x_3209_ == 0)
{
lean_dec_ref(v_proof_3208_);
lean_dec(v_ref_3207_);
lean_dec_ref(v_proof_3205_);
lean_dec(v_ref_3204_);
return v___x_3209_;
}
else
{
uint8_t v___x_3210_; 
v___x_3210_ = l_Lean_Syntax_structEq(v_ref_3204_, v_ref_3207_);
if (v___x_3210_ == 0)
{
lean_dec_ref(v_proof_3208_);
lean_dec_ref(v_proof_3205_);
return v___x_3210_;
}
else
{
uint8_t v___x_3211_; 
v___x_3211_ = lean_expr_eqv(v_proof_3205_, v_proof_3208_);
lean_dec_ref(v_proof_3208_);
lean_dec_ref(v_proof_3205_);
return v___x_3211_;
}
}
}
else
{
uint8_t v___x_3212_; 
lean_dec_ref_known(v_x_3193_, 3);
lean_dec_ref(v_x_3194_);
v___x_3212_ = 0;
return v___x_3212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq___boxed(lean_object* v_x_3213_, lean_object* v_x_3214_){
_start:
{
uint8_t v_res_3215_; lean_object* v_r_3216_; 
v_res_3215_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq(v_x_3213_, v_x_3214_);
v_r_3216_ = lean_box(v_res_3215_);
return v_r_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key(lean_object* v_x_3219_){
_start:
{
lean_object* v_declName_3220_; 
v_declName_3220_ = lean_ctor_get(v_x_3219_, 0);
lean_inc(v_declName_3220_);
return v_declName_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key___boxed(lean_object* v_x_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key(v_x_3221_);
lean_dec_ref(v_x_3221_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_ofOrigin(lean_object* v_x_3223_){
_start:
{
switch(lean_obj_tag(v_x_3223_))
{
case 0:
{
lean_object* v_declName_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v_declName_3224_ = lean_ctor_get(v_x_3223_, 0);
lean_inc(v_declName_3224_);
lean_dec_ref_known(v_x_3223_, 1);
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v_declName_3224_);
v___x_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
return v___x_3226_;
}
case 1:
{
lean_object* v_fvarId_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3235_; 
v_fvarId_3227_ = lean_ctor_get(v_x_3223_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_x_3223_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3229_ = v_x_3223_;
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_fvarId_3227_);
lean_dec(v_x_3223_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_fvarId_3227_);
v___x_3232_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
return v___x_3233_;
}
}
}
default: 
{
lean_object* v___x_3236_; 
lean_dec_ref(v_x_3223_);
v___x_3236_ = lean_box(0);
return v___x_3236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_getProof(lean_object* v_x_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
switch(lean_obj_tag(v_x_3237_))
{
case 0:
{
lean_object* v_declName_3243_; lean_object* v___x_3244_; 
v_declName_3243_ = lean_ctor_get(v_x_3237_, 0);
lean_inc_n(v_declName_3243_, 2);
lean_dec_ref_known(v_x_3237_, 1);
v___x_3244_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_3243_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3257_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3257_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3257_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3249_ = l_Lean_ConstantInfo_levelParams(v_a_3245_);
lean_dec(v_a_3245_);
v___x_3250_ = lean_box(0);
lean_inc(v___x_3249_);
v___x_3251_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_3249_, v___x_3250_);
v___x_3252_ = l_Lean_mkConst(v_declName_3243_, v___x_3251_);
v___x_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3249_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v___x_3253_);
v___x_3255_ = v___x_3247_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v_declName_3243_);
v_a_3258_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3244_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3244_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3276_; 
v_fvarId_3266_ = lean_ctor_get(v_x_3237_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_x_3237_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3268_ = v_x_3237_;
v_isShared_3269_ = v_isSharedCheck_3276_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_fvarId_3266_);
lean_dec(v_x_3237_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3276_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3270_ = lean_box(0);
v___x_3271_ = l_Lean_mkFVar(v_fvarId_3266_);
v___x_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3270_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set_tag(v___x_3268_, 0);
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
default: 
{
lean_object* v_proof_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_proof_3277_ = lean_ctor_get(v_x_3237_, 2);
lean_inc_ref(v_proof_3277_);
lean_dec_ref_known(v_x_3237_, 3);
v___x_3278_ = lean_box(0);
v___x_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v_proof_3277_);
v___x_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
return v___x_3280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_getProof___boxed(lean_object* v_x_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_getProof(v_x_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
lean_dec(v_a_3285_);
lean_dec_ref(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_a_3282_);
return v_res_3287_;
}
}
LEAN_EXPORT uint64_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof___lam__0(lean_object* v_sp_3288_){
_start:
{
lean_object* v___y_3290_; lean_object* v_declName_3293_; 
v_declName_3293_ = lean_ctor_get(v_sp_3288_, 0);
v___y_3290_ = v_declName_3293_;
goto v___jp_3289_;
v___jp_3289_:
{
if (lean_obj_tag(v___y_3290_) == 0)
{
uint64_t v___x_3291_; 
v___x_3291_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
return v___x_3291_;
}
else
{
uint64_t v_hash_3292_; 
v_hash_3292_ = lean_ctor_get_uint64(v___y_3290_, sizeof(void*)*2);
return v_hash_3292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof___lam__0___boxed(lean_object* v_sp_3294_){
_start:
{
uint64_t v_res_3295_; lean_object* v_r_3296_; 
v_res_3295_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instHashableSpecProof___lam__0(v_sp_3294_);
lean_dec_ref(v_sp_3294_);
v_r_3296_ = lean_box_uint64(v_res_3295_);
return v_r_3296_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__8(void){
_start:
{
lean_object* v___x_3320_; lean_object* v_dummy_3321_; 
v___x_3320_ = lean_box(0);
v_dummy_3321_ = l_Lean_Expr_sort___override(v___x_3320_);
return v_dummy_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f(lean_object* v_proof_3322_, lean_object* v_type_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_Meta_whnfR(v_type_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3382_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3382_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3382_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; 
v___x_3334_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1));
v___x_3335_ = lean_unsigned_to_nat(12u);
v___x_3336_ = l_Lean_Expr_isAppOfArity(v_a_3330_, v___x_3334_, v___x_3335_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v___x_3337_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5));
v___x_3338_ = lean_unsigned_to_nat(4u);
v___x_3339_ = l_Lean_Expr_isAppOfArity(v_a_3330_, v___x_3337_, v___x_3338_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
lean_dec(v_a_3330_);
lean_dec_ref(v_proof_3322_);
v___x_3340_ = lean_box(0);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3340_);
v___x_3342_ = v___x_3332_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3347_; 
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v_proof_3322_);
lean_ctor_set(v___x_3344_, 1, v_a_3330_);
v___x_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3345_);
v___x_3347_ = v___x_3332_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v_dummy_3353_; lean_object* v_nargs_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_del_object(v___x_3332_);
v___x_3349_ = l_Lean_Expr_getAppFn(v_a_3330_);
v___x_3350_ = l_Lean_Expr_constLevels_x21(v___x_3349_);
lean_dec_ref(v___x_3349_);
v___x_3351_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__7));
v___x_3352_ = l_Lean_Expr_const___override(v___x_3351_, v___x_3350_);
v_dummy_3353_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__8, &l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__8_once, _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__8);
v_nargs_3354_ = l_Lean_Expr_getAppNumArgs(v_a_3330_);
lean_inc(v_nargs_3354_);
v___x_3355_ = lean_mk_array(v_nargs_3354_, v_dummy_3353_);
v___x_3356_ = lean_unsigned_to_nat(1u);
v___x_3357_ = lean_nat_sub(v_nargs_3354_, v___x_3356_);
lean_dec(v_nargs_3354_);
v___x_3358_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3330_, v___x_3355_, v___x_3357_);
v___x_3359_ = lean_array_push(v___x_3358_, v_proof_3322_);
v___x_3360_ = l_Lean_mkAppN(v___x_3352_, v___x_3359_);
lean_dec_ref(v___x_3359_);
lean_inc(v_a_3327_);
lean_inc_ref(v_a_3326_);
lean_inc(v_a_3325_);
lean_inc_ref(v_a_3324_);
lean_inc_ref(v___x_3360_);
v___x_3361_ = lean_infer_type(v___x_3360_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3373_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3361_, 1);
v___x_3363_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_a_3362_, v_a_3325_);
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3373_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3373_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3360_);
lean_ctor_set(v___x_3368_, 1, v_a_3364_);
v___x_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3369_);
v___x_3371_ = v___x_3366_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec_ref(v___x_3360_);
v_a_3374_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3361_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3361_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec_ref(v_proof_3322_);
v_a_3383_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3329_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3329_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___boxed(lean_object* v_proof_3391_, lean_object* v_type_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f(v_proof_3391_, v_type_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_instantiate(lean_object* v_proof_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v_prf_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; 
switch(lean_obj_tag(v_proof_3399_))
{
case 0:
{
lean_object* v_declName_3461_; lean_object* v___x_3462_; 
v_declName_3461_ = lean_ctor_get(v_proof_3399_, 0);
lean_inc(v_declName_3461_);
lean_dec_ref_known(v_proof_3399_, 1);
v___x_3462_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_3461_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref_known(v___x_3462_, 1);
v_prf_3406_ = v_a_3463_;
v___y_3407_ = v_a_3400_;
v___y_3408_ = v_a_3401_;
v___y_3409_ = v_a_3402_;
v___y_3410_ = v_a_3403_;
goto v___jp_3405_;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
v_a_3464_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3462_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3462_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3472_; lean_object* v___x_3473_; 
v_fvarId_3472_ = lean_ctor_get(v_proof_3399_, 0);
lean_inc(v_fvarId_3472_);
lean_dec_ref_known(v_proof_3399_, 1);
v___x_3473_ = l_Lean_mkFVar(v_fvarId_3472_);
v_prf_3406_ = v___x_3473_;
v___y_3407_ = v_a_3400_;
v___y_3408_ = v_a_3401_;
v___y_3409_ = v_a_3402_;
v___y_3410_ = v_a_3403_;
goto v___jp_3405_;
}
default: 
{
lean_object* v_proof_3474_; 
v_proof_3474_ = lean_ctor_get(v_proof_3399_, 2);
lean_inc_ref(v_proof_3474_);
lean_dec_ref_known(v_proof_3399_, 3);
v_prf_3406_ = v_proof_3474_;
v___y_3407_ = v_a_3400_;
v___y_3408_ = v_a_3401_;
v___y_3409_ = v_a_3402_;
v___y_3410_ = v_a_3403_;
goto v___jp_3405_;
}
}
v___jp_3405_:
{
lean_object* v___x_3411_; 
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc_ref(v_prf_3406_);
v___x_3411_ = lean_infer_type(v_prf_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v___x_3413_; lean_object* v_a_3414_; uint8_t v___x_3415_; lean_object* v___x_3416_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3411_, 1);
v___x_3413_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_a_3412_, v___y_3408_);
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref(v___x_3413_);
v___x_3415_ = 0;
v___x_3416_ = l_Lean_Meta_forallMetaTelescope(v_a_3414_, v___x_3415_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3444_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3444_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3444_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_snd_3421_; lean_object* v_fst_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3443_; 
v_snd_3421_ = lean_ctor_get(v_a_3417_, 1);
v_fst_3422_ = lean_ctor_get(v_a_3417_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_a_3417_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3424_ = v_a_3417_;
v_isShared_3425_ = v_isSharedCheck_3443_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3421_);
lean_inc(v_fst_3422_);
lean_dec(v_a_3417_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3443_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_fst_3426_; lean_object* v_snd_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3442_; 
v_fst_3426_ = lean_ctor_get(v_snd_3421_, 0);
v_snd_3427_ = lean_ctor_get(v_snd_3421_, 1);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_snd_3421_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3429_ = v_snd_3421_;
v_isShared_3430_ = v_isSharedCheck_3442_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_snd_3427_);
lean_inc(v_fst_3426_);
lean_dec(v_snd_3421_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3442_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_inc(v_fst_3422_);
v___x_3431_ = l_Lean_Expr_beta(v_prf_3406_, v_fst_3422_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3431_);
v___x_3433_ = v___x_3429_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_snd_3427_);
v___x_3433_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3435_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3433_);
lean_ctor_set(v___x_3424_, 0, v_fst_3426_);
v___x_3435_ = v___x_3424_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v_fst_3422_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3436_);
v___x_3438_ = v___x_3419_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec_ref(v_prf_3406_);
v_a_3445_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3416_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3416_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref(v_prf_3406_);
v_a_3453_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3411_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3411_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_instantiate___boxed(lean_object* v_proof_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_instantiate(v_proof_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instToMessageDataSpecProof___lam__0(lean_object* v_x_3482_){
_start:
{
switch(lean_obj_tag(v_x_3482_))
{
case 0:
{
lean_object* v_declName_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_declName_3483_ = lean_ctor_get(v_x_3482_, 0);
lean_inc(v_declName_3483_);
lean_dec_ref_known(v_x_3482_, 1);
v___x_3484_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1);
v___x_3485_ = l_Lean_MessageData_ofName(v_declName_3483_);
v___x_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3484_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
return v___x_3486_;
}
case 1:
{
lean_object* v_fvarId_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v_fvarId_3487_ = lean_ctor_get(v_x_3482_, 0);
lean_inc(v_fvarId_3487_);
lean_dec_ref_known(v_x_3482_, 1);
v___x_3488_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3);
v___x_3489_ = l_Lean_mkFVar(v_fvarId_3487_);
v___x_3490_ = l_Lean_MessageData_ofExpr(v___x_3489_);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3488_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
return v___x_3491_;
}
default: 
{
lean_object* v_ref_3492_; lean_object* v_proof_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v_ref_3492_ = lean_ctor_get(v_x_3482_, 1);
lean_inc(v_ref_3492_);
v_proof_3493_ = lean_ctor_get(v_x_3482_, 2);
lean_inc_ref(v_proof_3493_);
lean_dec_ref_known(v_x_3482_, 3);
v___x_3494_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5);
v___x_3495_ = l_Lean_MessageData_ofSyntax(v_ref_3492_);
v___x_3496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3494_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v___x_3497_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7);
v___x_3498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3496_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
v___x_3499_ = l_Lean_MessageData_ofExpr(v_proof_3493_);
v___x_3500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3498_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
return v___x_3500_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default___closed__0(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3503_ = lean_unsigned_to_nat(1000u);
v___x_3504_ = lean_box(0);
v___x_3505_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecProof_default));
v___x_3506_ = l_Lean_Meta_Sym_instInhabitedPattern_default;
v___x_3507_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
lean_ctor_set(v___x_3507_, 1, v___x_3505_);
lean_ctor_set(v___x_3507_, 2, v___x_3504_);
lean_ctor_set(v___x_3507_, 3, v___x_3503_);
return v___x_3507_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default(void){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default___closed__0, &l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default___closed__0);
return v___x_3508_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem(void){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default;
return v___x_3509_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem___lam__0(lean_object* v_a_3510_, lean_object* v_b_3511_){
_start:
{
lean_object* v_proof_3512_; lean_object* v_proof_3513_; uint8_t v___x_3514_; 
v_proof_3512_ = lean_ctor_get(v_a_3510_, 1);
lean_inc_ref(v_proof_3512_);
lean_dec_ref(v_a_3510_);
v_proof_3513_ = lean_ctor_get(v_b_3511_, 1);
lean_inc_ref(v_proof_3513_);
lean_dec_ref(v_b_3511_);
v___x_3514_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq(v_proof_3512_, v_proof_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem___lam__0___boxed(lean_object* v_a_3515_, lean_object* v_b_3516_){
_start:
{
uint8_t v_res_3517_; lean_object* v_r_3518_; 
v_res_3517_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecTheorem___lam__0(v_a_3515_, v_b_3516_);
v_r_3518_ = lean_box(v_res_3517_);
return v_r_3518_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0);
v___x_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0(lean_object* v_00_u03b2_3524_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1);
return v___x_3525_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_3526_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default_spec__0(lean_box(0));
return v___x_3527_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3528_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__1, &l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__1);
v___x_3529_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__0, &l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__0);
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v___x_3528_);
return v___x_3530_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default(void){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__2, &l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__2);
return v___x_3531_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems(void){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default;
return v___x_3532_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__3(lean_object* v_msg_3534_){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__3___closed__0);
v___x_3536_ = lean_panic_fn_borrowed(v___x_3535_, v_msg_3534_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_vs_3537_, lean_object* v_v_3538_, lean_object* v_i_3539_){
_start:
{
lean_object* v___x_3540_; uint8_t v___x_3541_; 
v___x_3540_ = lean_array_get_size(v_vs_3537_);
v___x_3541_ = lean_nat_dec_lt(v_i_3539_, v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; 
lean_dec(v_i_3539_);
v___x_3542_ = lean_array_push(v_vs_3537_, v_v_3538_);
return v___x_3542_;
}
else
{
lean_object* v_proof_3543_; lean_object* v___x_3544_; lean_object* v_proof_3545_; uint8_t v___x_3546_; 
v_proof_3543_ = lean_ctor_get(v_v_3538_, 1);
v___x_3544_ = lean_array_fget_borrowed(v_vs_3537_, v_i_3539_);
v_proof_3545_ = lean_ctor_get(v___x_3544_, 1);
lean_inc_ref(v_proof_3545_);
lean_inc_ref(v_proof_3543_);
v___x_3546_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq(v_proof_3543_, v_proof_3545_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_add(v_i_3539_, v___x_3547_);
lean_dec(v_i_3539_);
v_i_3539_ = v___x_3548_;
goto _start;
}
else
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_array_fset(v_vs_3537_, v_i_3539_, v_v_3538_);
lean_dec(v_i_3539_);
return v___x_3550_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_vs_3551_, lean_object* v_v_3552_){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = lean_unsigned_to_nat(0u);
v___x_3554_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4(v_vs_3551_, v_v_3552_, v___x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1(lean_object* v_a_3555_, lean_object* v_b_3556_){
_start:
{
lean_object* v_fst_3557_; lean_object* v_fst_3558_; uint8_t v___x_3559_; 
v_fst_3557_ = lean_ctor_get(v_a_3555_, 0);
v_fst_3558_ = lean_ctor_get(v_b_3556_, 0);
v___x_3559_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_3557_, v_fst_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1___boxed(lean_object* v_a_3560_, lean_object* v_b_3561_){
_start:
{
uint8_t v_res_3562_; lean_object* v_r_3563_; 
v_res_3562_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1(v_a_3560_, v_b_3561_);
lean_dec_ref(v_b_3561_);
lean_dec_ref(v_a_3560_);
v_r_3563_ = lean_box(v_res_3562_);
return v_r_3563_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__0(lean_object* v_x_3564_, lean_object* v_keys_3565_, lean_object* v_v_3566_, lean_object* v_k_3567_, lean_object* v_x_3568_){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v_c_3571_; lean_object* v___x_3572_; 
v___x_3569_ = lean_unsigned_to_nat(1u);
v___x_3570_ = lean_nat_add(v_x_3564_, v___x_3569_);
v_c_3571_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_3565_, v_v_3566_, v___x_3570_);
lean_dec(v___x_3570_);
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v_k_3567_);
lean_ctor_set(v___x_3572_, 1, v_c_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__0___boxed(lean_object* v_x_3573_, lean_object* v_keys_3574_, lean_object* v_v_3575_, lean_object* v_k_3576_, lean_object* v_x_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__0(v_x_3573_, v_keys_3574_, v_v_3575_, v_k_3576_, v_x_3577_);
lean_dec_ref(v_keys_3574_);
lean_dec(v_x_3573_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_3583_, lean_object* v_keys_3584_, lean_object* v_v_3585_, lean_object* v_k_3586_, lean_object* v_as_3587_, lean_object* v_k_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v_mid_3593_; lean_object* v_midVal_3594_; uint8_t v___x_3595_; 
v___x_3591_ = lean_nat_add(v_x_3589_, v_x_3590_);
v___x_3592_ = lean_unsigned_to_nat(1u);
v_mid_3593_ = lean_nat_shiftr(v___x_3591_, v___x_3592_);
lean_dec(v___x_3591_);
v_midVal_3594_ = lean_array_fget(v_as_3587_, v_mid_3593_);
v___x_3595_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1(v_midVal_3594_, v_k_3588_);
if (v___x_3595_ == 0)
{
uint8_t v___x_3596_; 
lean_dec(v_x_3590_);
v___x_3596_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1(v_k_3588_, v_midVal_3594_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; uint8_t v___x_3598_; 
lean_dec(v_x_3589_);
v___x_3597_ = lean_array_get_size(v_as_3587_);
v___x_3598_ = lean_nat_dec_lt(v_mid_3593_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_dec(v_midVal_3594_);
lean_dec(v_mid_3593_);
lean_dec(v_k_3586_);
lean_dec_ref(v_v_3585_);
return v_as_3587_;
}
else
{
lean_object* v_snd_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3611_; 
v_snd_3599_ = lean_ctor_get(v_midVal_3594_, 1);
v_isSharedCheck_3611_ = !lean_is_exclusive(v_midVal_3594_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; 
v_unused_3612_ = lean_ctor_get(v_midVal_3594_, 0);
lean_dec(v_unused_3612_);
v___x_3601_ = v_midVal_3594_;
v_isShared_3602_ = v_isSharedCheck_3611_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_snd_3599_);
lean_dec(v_midVal_3594_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3611_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3603_; lean_object* v_xs_x27_3604_; lean_object* v___x_3605_; lean_object* v_c_3606_; lean_object* v___x_3608_; 
v___x_3603_ = lean_box(0);
v_xs_x27_3604_ = lean_array_fset(v_as_3587_, v_mid_3593_, v___x_3603_);
v___x_3605_ = lean_nat_add(v_x_3583_, v___x_3592_);
v_c_3606_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(v_keys_3584_, v_v_3585_, v___x_3605_, v_snd_3599_);
lean_dec(v___x_3605_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 1, v_c_3606_);
lean_ctor_set(v___x_3601_, 0, v_k_3586_);
v___x_3608_ = v___x_3601_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_k_3586_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_c_3606_);
v___x_3608_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; 
v___x_3609_ = lean_array_fset(v_xs_x27_3604_, v_mid_3593_, v___x_3608_);
lean_dec(v_mid_3593_);
return v___x_3609_;
}
}
}
}
else
{
lean_dec(v_midVal_3594_);
v_x_3590_ = v_mid_3593_;
goto _start;
}
}
else
{
uint8_t v___x_3614_; 
lean_dec(v_midVal_3594_);
v___x_3614_ = lean_nat_dec_eq(v_mid_3593_, v_x_3589_);
if (v___x_3614_ == 0)
{
lean_dec(v_x_3589_);
v_x_3589_ = v_mid_3593_;
goto _start;
}
else
{
lean_object* v___x_3616_; lean_object* v_c_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v_j_3620_; lean_object* v_as_3621_; lean_object* v___x_3622_; 
lean_dec(v_mid_3593_);
lean_dec(v_x_3590_);
v___x_3616_ = lean_nat_add(v_x_3583_, v___x_3592_);
v_c_3617_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_3584_, v_v_3585_, v___x_3616_);
lean_dec(v___x_3616_);
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v_k_3586_);
lean_ctor_set(v___x_3618_, 1, v_c_3617_);
v___x_3619_ = lean_nat_add(v_x_3589_, v___x_3592_);
lean_dec(v_x_3589_);
v_j_3620_ = lean_array_get_size(v_as_3587_);
v_as_3621_ = lean_array_push(v_as_3587_, v___x_3618_);
v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_3619_, v_as_3621_, v_j_3620_);
lean_dec(v___x_3619_);
return v___x_3622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3623_, lean_object* v_keys_3624_, lean_object* v_v_3625_, lean_object* v_k_3626_, lean_object* v_as_3627_, lean_object* v_k_3628_){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3629_ = lean_array_get_size(v_as_3627_);
v___x_3630_ = lean_unsigned_to_nat(0u);
v___x_3631_ = lean_nat_dec_eq(v___x_3629_, v___x_3630_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3632_ = lean_array_fget_borrowed(v_as_3627_, v___x_3630_);
v___x_3633_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1(v_k_3628_, v___x_3632_);
if (v___x_3633_ == 0)
{
uint8_t v___x_3634_; 
v___x_3634_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1(v___x_3632_, v_k_3628_);
if (v___x_3634_ == 0)
{
uint8_t v___x_3635_; 
v___x_3635_ = lean_nat_dec_lt(v___x_3630_, v___x_3629_);
if (v___x_3635_ == 0)
{
lean_dec(v_k_3626_);
lean_dec_ref(v_v_3625_);
return v_as_3627_;
}
else
{
lean_object* v___x_3636_; lean_object* v_xs_x27_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
lean_inc(v___x_3632_);
v___x_3636_ = lean_box(0);
v_xs_x27_3637_ = lean_array_fset(v_as_3627_, v___x_3630_, v___x_3636_);
v___x_3638_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__2(v_x_3623_, v_keys_3624_, v_v_3625_, v_k_3626_, v___x_3632_);
v___x_3639_ = lean_array_fset(v_xs_x27_3637_, v___x_3630_, v___x_3638_);
return v___x_3639_;
}
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; 
v___x_3640_ = lean_unsigned_to_nat(1u);
v___x_3641_ = lean_nat_sub(v___x_3629_, v___x_3640_);
v___x_3642_ = lean_array_fget_borrowed(v_as_3627_, v___x_3641_);
v___x_3643_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1(v___x_3642_, v_k_3628_);
if (v___x_3643_ == 0)
{
uint8_t v___x_3644_; 
v___x_3644_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__1(v_k_3628_, v___x_3642_);
if (v___x_3644_ == 0)
{
uint8_t v___x_3645_; 
v___x_3645_ = lean_nat_dec_lt(v___x_3641_, v___x_3629_);
if (v___x_3645_ == 0)
{
lean_dec(v___x_3641_);
lean_dec(v_k_3626_);
lean_dec_ref(v_v_3625_);
return v_as_3627_;
}
else
{
lean_object* v___x_3646_; lean_object* v_xs_x27_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_inc(v___x_3642_);
v___x_3646_ = lean_box(0);
v_xs_x27_3647_ = lean_array_fset(v_as_3627_, v___x_3641_, v___x_3646_);
v___x_3648_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__2(v_x_3623_, v_keys_3624_, v_v_3625_, v_k_3626_, v___x_3642_);
v___x_3649_ = lean_array_fset(v_xs_x27_3647_, v___x_3641_, v___x_3648_);
lean_dec(v___x_3641_);
return v___x_3649_;
}
}
else
{
lean_object* v___x_3650_; 
v___x_3650_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_x_3623_, v_keys_3624_, v_v_3625_, v_k_3626_, v_as_3627_, v_k_3628_, v___x_3630_, v___x_3641_);
return v___x_3650_;
}
}
else
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
lean_dec(v___x_3641_);
v___x_3651_ = lean_box(0);
v___x_3652_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__0(v_x_3623_, v_keys_3624_, v_v_3625_, v_k_3626_, v___x_3651_);
v___x_3653_ = lean_array_push(v_as_3627_, v___x_3652_);
return v___x_3653_;
}
}
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v_as_3656_; lean_object* v___x_3657_; 
v___x_3654_ = lean_box(0);
v___x_3655_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__0(v_x_3623_, v_keys_3624_, v_v_3625_, v_k_3626_, v___x_3654_);
v_as_3656_ = lean_array_push(v_as_3627_, v___x_3655_);
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_3630_, v_as_3656_, v___x_3629_);
return v___x_3657_;
}
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = lean_box(0);
v___x_3659_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__0(v_x_3623_, v_keys_3624_, v_v_3625_, v_k_3626_, v___x_3658_);
v___x_3660_ = lean_array_push(v_as_3627_, v___x_3659_);
return v___x_3660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(lean_object* v_keys_3661_, lean_object* v_v_3662_, lean_object* v_x_3663_, lean_object* v_x_3664_){
_start:
{
lean_object* v_vs_3665_; lean_object* v_children_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3683_; 
v_vs_3665_ = lean_ctor_get(v_x_3664_, 0);
v_children_3666_ = lean_ctor_get(v_x_3664_, 1);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_x_3664_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3668_ = v_x_3664_;
v_isShared_3669_ = v_isSharedCheck_3683_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_children_3666_);
lean_inc(v_vs_3665_);
lean_dec(v_x_3664_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3683_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3670_ = lean_array_get_size(v_keys_3661_);
v___x_3671_ = lean_nat_dec_lt(v_x_3663_, v___x_3670_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3672_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__2(v_vs_3665_, v_v_3662_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3672_);
v___x_3674_ = v___x_3668_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_children_3666_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
else
{
lean_object* v_k_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v_c_3679_; lean_object* v___x_3681_; 
v_k_3676_ = lean_array_fget_borrowed(v_keys_3661_, v_x_3663_);
v___x_3677_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___closed__1));
lean_inc_n(v_k_3676_, 2);
v___x_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3678_, 0, v_k_3676_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v_c_3679_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(v_x_3663_, v_keys_3661_, v_v_3662_, v_k_3676_, v_children_3666_, v___x_3678_);
lean_dec_ref_known(v___x_3678_, 2);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 1, v_c_3679_);
v___x_3681_ = v___x_3668_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_vs_3665_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_c_3679_);
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
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__2(lean_object* v_x_3684_, lean_object* v_keys_3685_, lean_object* v_v_3686_, lean_object* v_k_3687_, lean_object* v_x_3688_){
_start:
{
lean_object* v_snd_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3699_; 
v_snd_3689_ = lean_ctor_get(v_x_3688_, 1);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_x_3688_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v_x_3688_, 0);
lean_dec(v_unused_3700_);
v___x_3691_ = v_x_3688_;
v_isShared_3692_ = v_isSharedCheck_3699_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_snd_3689_);
lean_dec(v_x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3699_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v_c_3695_; lean_object* v___x_3697_; 
v___x_3693_ = lean_unsigned_to_nat(1u);
v___x_3694_ = lean_nat_add(v_x_3684_, v___x_3693_);
v_c_3695_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(v_keys_3685_, v_v_3686_, v___x_3694_, v_snd_3689_);
lean_dec(v___x_3694_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 1, v_c_3695_);
lean_ctor_set(v___x_3691_, 0, v_k_3687_);
v___x_3697_ = v___x_3691_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_k_3687_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_c_3695_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__2___boxed(lean_object* v_x_3701_, lean_object* v_keys_3702_, lean_object* v_v_3703_, lean_object* v_k_3704_, lean_object* v_x_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___lam__2(v_x_3701_, v_keys_3702_, v_v_3703_, v_k_3704_, v_x_3705_);
lean_dec_ref(v_keys_3702_);
lean_dec(v_x_3701_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_keys_3707_, lean_object* v_v_3708_, lean_object* v_x_3709_, lean_object* v_x_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(v_keys_3707_, v_v_3708_, v_x_3709_, v_x_3710_);
lean_dec(v_x_3709_);
lean_dec_ref(v_keys_3707_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_3712_, lean_object* v_keys_3713_, lean_object* v_v_3714_, lean_object* v_k_3715_, lean_object* v_as_3716_, lean_object* v_k_3717_, lean_object* v_x_3718_, lean_object* v_x_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_x_3712_, v_keys_3713_, v_v_3714_, v_k_3715_, v_as_3716_, v_k_3717_, v_x_3718_, v_x_3719_);
lean_dec_ref(v_k_3717_);
lean_dec_ref(v_keys_3713_);
lean_dec(v_x_3712_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3721_, lean_object* v_keys_3722_, lean_object* v_v_3723_, lean_object* v_k_3724_, lean_object* v_as_3725_, lean_object* v_k_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(v_x_3721_, v_keys_3722_, v_v_3723_, v_k_3724_, v_as_3725_, v_k_3726_);
lean_dec_ref(v_k_3726_);
lean_dec_ref(v_keys_3722_);
lean_dec(v_x_3721_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(lean_object* v_keys_3728_, lean_object* v_v_3729_, lean_object* v_x_3730_){
_start:
{
if (lean_obj_tag(v_x_3730_) == 0)
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3731_ = lean_unsigned_to_nat(1u);
v___x_3732_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_3728_, v_v_3729_, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
return v___x_3733_;
}
else
{
lean_object* v_val_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3743_; 
v_val_3734_ = lean_ctor_get(v_x_3730_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_x_3730_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3736_ = v_x_3730_;
v_isShared_3737_ = v_isSharedCheck_3743_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_val_3734_);
lean_dec(v_x_3730_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3743_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3741_; 
v___x_3738_ = lean_unsigned_to_nat(1u);
v___x_3739_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(v_keys_3728_, v_v_3729_, v___x_3738_, v_val_3734_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v___x_3739_);
v___x_3741_ = v___x_3736_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_keys_3744_, lean_object* v_v_3745_, lean_object* v_x_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(v_keys_3744_, v_v_3745_, v_x_3746_);
lean_dec_ref(v_keys_3744_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2(lean_object* v_keys_3748_, lean_object* v_v_3749_, lean_object* v_x_3750_, size_t v_x_3751_, size_t v_x_3752_, lean_object* v_x_3753_){
_start:
{
if (lean_obj_tag(v_x_3750_) == 0)
{
lean_object* v_es_3754_; size_t v___x_3755_; size_t v___x_3756_; size_t v___x_3757_; size_t v___x_3758_; lean_object* v_j_3759_; lean_object* v___x_3760_; uint8_t v___x_3761_; 
v_es_3754_ = lean_ctor_get(v_x_3750_, 0);
v___x_3755_ = ((size_t)5ULL);
v___x_3756_ = ((size_t)1ULL);
v___x_3757_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1);
v___x_3758_ = lean_usize_land(v_x_3751_, v___x_3757_);
v_j_3759_ = lean_usize_to_nat(v___x_3758_);
v___x_3760_ = lean_array_get_size(v_es_3754_);
v___x_3761_ = lean_nat_dec_lt(v_j_3759_, v___x_3760_);
if (v___x_3761_ == 0)
{
lean_dec(v_j_3759_);
lean_dec(v_x_3753_);
lean_dec_ref(v_v_3749_);
return v_x_3750_;
}
else
{
lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3827_; 
lean_inc_ref(v_es_3754_);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_x_3750_);
if (v_isSharedCheck_3827_ == 0)
{
lean_object* v_unused_3828_; 
v_unused_3828_ = lean_ctor_get(v_x_3750_, 0);
lean_dec(v_unused_3828_);
v___x_3763_ = v_x_3750_;
v_isShared_3764_ = v_isSharedCheck_3827_;
goto v_resetjp_3762_;
}
else
{
lean_dec(v_x_3750_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3827_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_v_3765_; lean_object* v___x_3766_; lean_object* v_xs_x27_3767_; lean_object* v___y_3769_; 
v_v_3765_ = lean_array_fget(v_es_3754_, v_j_3759_);
v___x_3766_ = lean_box(0);
v_xs_x27_3767_ = lean_array_fset(v_es_3754_, v_j_3759_, v___x_3766_);
switch(lean_obj_tag(v_v_3765_))
{
case 0:
{
lean_object* v_key_3774_; lean_object* v_val_3775_; uint8_t v___x_3776_; 
v_key_3774_ = lean_ctor_get(v_v_3765_, 0);
v_val_3775_ = lean_ctor_get(v_v_3765_, 1);
v___x_3776_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_3753_, v_key_3774_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3777_ = lean_box(0);
v___x_3778_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(v_keys_3748_, v_v_3749_, v___x_3777_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_dec(v_x_3753_);
v___y_3769_ = v_v_3765_;
goto v___jp_3768_;
}
else
{
lean_object* v_val_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3787_; 
lean_inc(v_val_3775_);
lean_inc(v_key_3774_);
lean_dec_ref_known(v_v_3765_, 2);
v_val_3779_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3781_ = v___x_3778_;
v_isShared_3782_ = v_isSharedCheck_3787_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_val_3779_);
lean_dec(v___x_3778_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3787_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3783_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3774_, v_val_3775_, v_x_3753_, v_val_3779_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v___x_3783_);
v___x_3785_ = v___x_3781_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
v___y_3769_ = v___x_3785_;
goto v___jp_3768_;
}
}
}
}
else
{
lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3798_; 
lean_inc(v_val_3775_);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_v_3765_);
if (v_isSharedCheck_3798_ == 0)
{
lean_object* v_unused_3799_; lean_object* v_unused_3800_; 
v_unused_3799_ = lean_ctor_get(v_v_3765_, 1);
lean_dec(v_unused_3799_);
v_unused_3800_ = lean_ctor_get(v_v_3765_, 0);
lean_dec(v_unused_3800_);
v___x_3789_ = v_v_3765_;
v_isShared_3790_ = v_isSharedCheck_3798_;
goto v_resetjp_3788_;
}
else
{
lean_dec(v_v_3765_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3798_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3791_, 0, v_val_3775_);
v___x_3792_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(v_keys_3748_, v_v_3749_, v___x_3791_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v___x_3793_; 
lean_del_object(v___x_3789_);
lean_dec(v_x_3753_);
v___x_3793_ = lean_box(2);
v___y_3769_ = v___x_3793_;
goto v___jp_3768_;
}
else
{
lean_object* v_val_3794_; lean_object* v___x_3796_; 
v_val_3794_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_val_3794_);
lean_dec_ref_known(v___x_3792_, 1);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 1, v_val_3794_);
lean_ctor_set(v___x_3789_, 0, v_x_3753_);
v___x_3796_ = v___x_3789_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_x_3753_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_val_3794_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
v___y_3769_ = v___x_3796_;
goto v___jp_3768_;
}
}
}
}
}
case 1:
{
lean_object* v_node_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3822_; 
v_node_3801_ = lean_ctor_get(v_v_3765_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_v_3765_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3803_ = v_v_3765_;
v_isShared_3804_ = v_isSharedCheck_3822_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_node_3801_);
lean_dec(v_v_3765_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3822_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
size_t v___x_3805_; size_t v___x_3806_; lean_object* v_newNode_3807_; lean_object* v___x_3808_; 
v___x_3805_ = lean_usize_shift_right(v_x_3751_, v___x_3755_);
v___x_3806_ = lean_usize_add(v_x_3752_, v___x_3756_);
v_newNode_3807_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2(v_keys_3748_, v_v_3749_, v_node_3801_, v___x_3805_, v___x_3806_, v_x_3753_);
lean_inc_ref(v_newNode_3807_);
v___x_3808_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_3807_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v___x_3810_; 
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 0, v_newNode_3807_);
v___x_3810_ = v___x_3803_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_newNode_3807_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
v___y_3769_ = v___x_3810_;
goto v___jp_3768_;
}
}
else
{
lean_object* v_val_3812_; lean_object* v_fst_3813_; lean_object* v_snd_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref(v_newNode_3807_);
lean_del_object(v___x_3803_);
v_val_3812_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_val_3812_);
lean_dec_ref_known(v___x_3808_, 1);
v_fst_3813_ = lean_ctor_get(v_val_3812_, 0);
v_snd_3814_ = lean_ctor_get(v_val_3812_, 1);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_val_3812_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v_val_3812_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_snd_3814_);
lean_inc(v_fst_3813_);
lean_dec(v_val_3812_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_fst_3813_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_snd_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
v___y_3769_ = v___x_3819_;
goto v___jp_3768_;
}
}
}
}
}
default: 
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = lean_box(0);
v___x_3824_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(v_keys_3748_, v_v_3749_, v___x_3823_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_dec(v_x_3753_);
v___y_3769_ = v_v_3765_;
goto v___jp_3768_;
}
else
{
lean_object* v_val_3825_; lean_object* v___x_3826_; 
v_val_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_val_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v___x_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3826_, 0, v_x_3753_);
lean_ctor_set(v___x_3826_, 1, v_val_3825_);
v___y_3769_ = v___x_3826_;
goto v___jp_3768_;
}
}
}
v___jp_3768_:
{
lean_object* v___x_3770_; lean_object* v___x_3772_; 
v___x_3770_ = lean_array_fset(v_xs_x27_3767_, v_j_3759_, v___y_3769_);
lean_dec(v_j_3759_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3770_);
v___x_3772_ = v___x_3763_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
else
{
lean_object* v_ks_3829_; lean_object* v_vs_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3863_; 
v_ks_3829_ = lean_ctor_get(v_x_3750_, 0);
v_vs_3830_ = lean_ctor_get(v_x_3750_, 1);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_x_3750_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3832_ = v_x_3750_;
v_isShared_3833_ = v_isSharedCheck_3863_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_vs_3830_);
lean_inc(v_ks_3829_);
lean_dec(v_x_3750_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3863_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__4(v_ks_3829_, v_x_3753_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v___x_3836_; 
if (v_isShared_3833_ == 0)
{
v___x_3836_ = v___x_3832_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_ks_3829_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_vs_3830_);
v___x_3836_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = lean_box(0);
v___x_3838_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(v_keys_3748_, v_v_3749_, v___x_3837_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_dec(v_x_3753_);
return v___x_3836_;
}
else
{
lean_object* v_val_3839_; lean_object* v___x_3840_; 
v_val_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_val_3839_);
lean_dec_ref_known(v___x_3838_, 1);
v___x_3840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg(v___x_3836_, v_x_3751_, v_x_3752_, v_x_3753_, v_val_3839_);
return v___x_3840_;
}
}
}
else
{
lean_object* v_val_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3862_; 
v_val_3842_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3844_ = v___x_3834_;
v_isShared_3845_ = v_isSharedCheck_3862_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_val_3842_);
lean_dec(v___x_3834_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3862_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v_v_x27_3846_; lean_object* v_keys_3847_; lean_object* v_vals_3848_; lean_object* v___x_3850_; 
v_v_x27_3846_ = lean_array_fget(v_vs_3830_, v_val_3842_);
lean_inc(v_val_3842_);
v_keys_3847_ = l_Array_eraseIdx___redArg(v_ks_3829_, v_val_3842_);
v_vals_3848_ = l_Array_eraseIdx___redArg(v_vs_3830_, v_val_3842_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 0, v_v_x27_3846_);
v___x_3850_ = v___x_3844_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_v_x27_3846_);
v___x_3850_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___lam__0(v_keys_3748_, v_v_3749_, v___x_3850_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v___x_3853_; 
lean_dec(v_x_3753_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 1, v_vals_3848_);
lean_ctor_set(v___x_3832_, 0, v_keys_3847_);
v___x_3853_ = v___x_3832_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_keys_3847_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_vals_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
else
{
lean_object* v_val_3855_; lean_object* v_keys_3856_; lean_object* v_vals_3857_; lean_object* v___x_3859_; 
v_val_3855_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_val_3855_);
lean_dec_ref_known(v___x_3851_, 1);
v_keys_3856_ = lean_array_push(v_keys_3847_, v_x_3753_);
v_vals_3857_ = lean_array_push(v_vals_3848_, v_val_3855_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 1, v_vals_3857_);
lean_ctor_set(v___x_3832_, 0, v_keys_3856_);
v___x_3859_ = v___x_3832_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_keys_3856_);
lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_vals_3857_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_keys_3864_, lean_object* v_v_3865_, lean_object* v_x_3866_, lean_object* v_x_3867_, lean_object* v_x_3868_, lean_object* v_x_3869_){
_start:
{
size_t v_x_1594__boxed_3870_; size_t v_x_1595__boxed_3871_; lean_object* v_res_3872_; 
v_x_1594__boxed_3870_ = lean_unbox_usize(v_x_3867_);
lean_dec(v_x_3867_);
v_x_1595__boxed_3871_ = lean_unbox_usize(v_x_3868_);
lean_dec(v_x_3868_);
v_res_3872_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2(v_keys_3864_, v_v_3865_, v_x_3866_, v_x_1594__boxed_3870_, v_x_1595__boxed_3871_, v_x_3869_);
lean_dec_ref(v_keys_3864_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0(lean_object* v_d_3873_, lean_object* v_keys_3874_, lean_object* v_v_3875_){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; uint8_t v___x_3878_; 
v___x_3876_ = lean_array_get_size(v_keys_3874_);
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3878_ = lean_nat_dec_eq(v___x_3876_, v___x_3877_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; lean_object* v_k_3880_; uint64_t v___x_3881_; size_t v_h_3882_; size_t v___x_3883_; lean_object* v___x_3884_; 
v___x_3879_ = lean_box(0);
v_k_3880_ = lean_array_get_borrowed(v___x_3879_, v_keys_3874_, v___x_3877_);
v___x_3881_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_3880_);
v_h_3882_ = lean_uint64_to_usize(v___x_3881_);
v___x_3883_ = ((size_t)1ULL);
lean_inc(v_k_3880_);
v___x_3884_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__2(v_keys_3874_, v_v_3875_, v_d_3873_, v_h_3882_, v___x_3883_, v_k_3880_);
return v___x_3884_;
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
lean_dec_ref(v_v_3875_);
lean_dec_ref(v_d_3873_);
v___x_3885_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3);
v___x_3886_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__3(v___x_3885_);
return v___x_3886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0___boxed(lean_object* v_d_3887_, lean_object* v_keys_3888_, lean_object* v_v_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0(v_d_3887_, v_keys_3888_, v_v_3889_);
lean_dec_ref(v_keys_3888_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0(lean_object* v_d_3891_, lean_object* v_p_3892_, lean_object* v_v_3893_){
_start:
{
lean_object* v_keys_3894_; lean_object* v___x_3895_; 
v_keys_3894_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_3892_);
v___x_3895_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0(v_d_3891_, v_keys_3894_, v_v_3893_);
lean_dec_ref(v_keys_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert(lean_object* v_d_3896_, lean_object* v_e_3897_){
_start:
{
lean_object* v_specs_3898_; lean_object* v_erased_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3908_; 
v_specs_3898_ = lean_ctor_get(v_d_3896_, 0);
v_erased_3899_ = lean_ctor_get(v_d_3896_, 1);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_d_3896_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3901_ = v_d_3896_;
v_isShared_3902_ = v_isSharedCheck_3908_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_erased_3899_);
lean_inc(v_specs_3898_);
lean_dec(v_d_3896_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3908_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v_pattern_3903_; lean_object* v___x_3904_; lean_object* v___x_3906_; 
v_pattern_3903_ = lean_ctor_get(v_e_3897_, 0);
lean_inc_ref(v_pattern_3903_);
v___x_3904_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0(v_specs_3898_, v_pattern_3903_, v_e_3897_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3904_);
v___x_3906_ = v___x_3901_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_erased_3899_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_x_3909_, lean_object* v_keys_3910_, lean_object* v_v_3911_, lean_object* v_k_3912_, lean_object* v_as_3913_, lean_object* v_k_3914_, lean_object* v_x_3915_, lean_object* v_x_3916_, lean_object* v_x_3917_, lean_object* v_x_3918_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_x_3909_, v_keys_3910_, v_v_3911_, v_k_3912_, v_as_3913_, v_k_3914_, v_x_3915_, v_x_3916_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_x_3920_, lean_object* v_keys_3921_, lean_object* v_v_3922_, lean_object* v_k_3923_, lean_object* v_as_3924_, lean_object* v_k_3925_, lean_object* v_x_3926_, lean_object* v_x_3927_, lean_object* v_x_3928_, lean_object* v_x_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3_spec__6(v_x_3920_, v_keys_3921_, v_v_3922_, v_k_3923_, v_as_3924_, v_k_3925_, v_x_3926_, v_x_3927_, v_x_3928_, v_x_3929_);
lean_dec_ref(v_k_3925_);
lean_dec_ref(v_keys_3921_);
lean_dec(v_x_3920_);
return v_res_3930_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3931_, lean_object* v_i_3932_, lean_object* v_k_3933_){
_start:
{
lean_object* v___x_3934_; uint8_t v___x_3935_; 
v___x_3934_ = lean_array_get_size(v_keys_3931_);
v___x_3935_ = lean_nat_dec_lt(v_i_3932_, v___x_3934_);
if (v___x_3935_ == 0)
{
lean_dec_ref(v_k_3933_);
lean_dec(v_i_3932_);
return v___x_3935_;
}
else
{
lean_object* v_k_x27_3936_; uint8_t v___x_3937_; 
v_k_x27_3936_ = lean_array_fget_borrowed(v_keys_3931_, v_i_3932_);
lean_inc(v_k_x27_3936_);
lean_inc_ref(v_k_3933_);
v___x_3937_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq(v_k_3933_, v_k_x27_3936_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = lean_unsigned_to_nat(1u);
v___x_3939_ = lean_nat_add(v_i_3932_, v___x_3938_);
lean_dec(v_i_3932_);
v_i_3932_ = v___x_3939_;
goto _start;
}
else
{
lean_dec_ref(v_k_3933_);
lean_dec(v_i_3932_);
return v___x_3937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3941_, lean_object* v_i_3942_, lean_object* v_k_3943_){
_start:
{
uint8_t v_res_3944_; lean_object* v_r_3945_; 
v_res_3944_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_3941_, v_i_3942_, v_k_3943_);
lean_dec_ref(v_keys_3941_);
v_r_3945_ = lean_box(v_res_3944_);
return v_r_3945_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(lean_object* v_x_3946_, size_t v_x_3947_, lean_object* v_x_3948_){
_start:
{
if (lean_obj_tag(v_x_3946_) == 0)
{
lean_object* v_es_3949_; lean_object* v___x_3950_; size_t v___x_3951_; size_t v___x_3952_; size_t v___x_3953_; lean_object* v_j_3954_; lean_object* v___x_3955_; 
v_es_3949_ = lean_ctor_get(v_x_3946_, 0);
lean_inc_ref(v_es_3949_);
lean_dec_ref_known(v_x_3946_, 1);
v___x_3950_ = lean_box(2);
v___x_3951_ = ((size_t)5ULL);
v___x_3952_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1);
v___x_3953_ = lean_usize_land(v_x_3947_, v___x_3952_);
v_j_3954_ = lean_usize_to_nat(v___x_3953_);
v___x_3955_ = lean_array_get(v___x_3950_, v_es_3949_, v_j_3954_);
lean_dec(v_j_3954_);
lean_dec_ref(v_es_3949_);
switch(lean_obj_tag(v___x_3955_))
{
case 0:
{
lean_object* v_key_3956_; uint8_t v___x_3957_; 
v_key_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_key_3956_);
lean_dec_ref_known(v___x_3955_, 2);
v___x_3957_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq(v_x_3948_, v_key_3956_);
return v___x_3957_;
}
case 1:
{
lean_object* v_node_3958_; size_t v___x_3959_; 
v_node_3958_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_node_3958_);
lean_dec_ref_known(v___x_3955_, 1);
v___x_3959_ = lean_usize_shift_right(v_x_3947_, v___x_3951_);
v_x_3946_ = v_node_3958_;
v_x_3947_ = v___x_3959_;
goto _start;
}
default: 
{
uint8_t v___x_3961_; 
lean_dec_ref(v_x_3948_);
v___x_3961_ = 0;
return v___x_3961_;
}
}
}
else
{
lean_object* v_ks_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v_ks_3962_ = lean_ctor_get(v_x_3946_, 0);
lean_inc_ref(v_ks_3962_);
lean_dec_ref_known(v_x_3946_, 2);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_ks_3962_, v___x_3963_, v_x_3948_);
lean_dec_ref(v_ks_3962_);
return v___x_3964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg___boxed(lean_object* v_x_3965_, lean_object* v_x_3966_, lean_object* v_x_3967_){
_start:
{
size_t v_x_146__boxed_3968_; uint8_t v_res_3969_; lean_object* v_r_3970_; 
v_x_146__boxed_3968_ = lean_unbox_usize(v_x_3966_);
lean_dec(v_x_3966_);
v_res_3969_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_3965_, v_x_146__boxed_3968_, v_x_3967_);
v_r_3970_ = lean_box(v_res_3969_);
return v_r_3970_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0___redArg(lean_object* v_x_3971_, lean_object* v_x_3972_){
_start:
{
uint64_t v___y_3974_; lean_object* v___y_3978_; lean_object* v_declName_3981_; 
v_declName_3981_ = lean_ctor_get(v_x_3972_, 0);
lean_inc(v_declName_3981_);
v___y_3978_ = v_declName_3981_;
goto v___jp_3977_;
v___jp_3973_:
{
size_t v___x_3975_; uint8_t v___x_3976_; 
v___x_3975_ = lean_uint64_to_usize(v___y_3974_);
v___x_3976_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_3971_, v___x_3975_, v_x_3972_);
return v___x_3976_;
}
v___jp_3977_:
{
if (lean_obj_tag(v___y_3978_) == 0)
{
uint64_t v___x_3979_; 
v___x_3979_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_3974_ = v___x_3979_;
goto v___jp_3973_;
}
else
{
uint64_t v_hash_3980_; 
v_hash_3980_ = lean_ctor_get_uint64(v___y_3978_, sizeof(void*)*2);
lean_dec(v___y_3978_);
v___y_3974_ = v_hash_3980_;
goto v___jp_3973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0___redArg___boxed(lean_object* v_x_3982_, lean_object* v_x_3983_){
_start:
{
uint8_t v_res_3984_; lean_object* v_r_3985_; 
v_res_3984_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_3982_, v_x_3983_);
v_r_3985_ = lean_box(v_res_3984_);
return v_r_3985_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased(lean_object* v_d_3986_, lean_object* v_thmId_3987_){
_start:
{
lean_object* v_erased_3988_; uint8_t v___x_3989_; 
v_erased_3988_ = lean_ctor_get(v_d_3986_, 1);
lean_inc_ref(v_erased_3988_);
lean_dec_ref(v_d_3986_);
v___x_3989_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_erased_3988_, v_thmId_3987_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased___boxed(lean_object* v_d_3990_, lean_object* v_thmId_3991_){
_start:
{
uint8_t v_res_3992_; lean_object* v_r_3993_; 
v_res_3992_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased(v_d_3990_, v_thmId_3991_);
v_r_3993_ = lean_box(v_res_3992_);
return v_r_3993_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0(lean_object* v_00_u03b2_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_){
_start:
{
uint8_t v___x_3997_; 
v___x_3997_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_3995_, v_x_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0___boxed(lean_object* v_00_u03b2_3998_, lean_object* v_x_3999_, lean_object* v_x_4000_){
_start:
{
uint8_t v_res_4001_; lean_object* v_r_4002_; 
v_res_4001_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0(v_00_u03b2_3998_, v_x_3999_, v_x_4000_);
v_r_4002_ = lean_box(v_res_4001_);
return v_r_4002_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(lean_object* v_00_u03b2_4003_, lean_object* v_x_4004_, size_t v_x_4005_, lean_object* v_x_4006_){
_start:
{
uint8_t v___x_4007_; 
v___x_4007_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_4004_, v_x_4005_, v_x_4006_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4008_, lean_object* v_x_4009_, lean_object* v_x_4010_, lean_object* v_x_4011_){
_start:
{
size_t v_x_228__boxed_4012_; uint8_t v_res_4013_; lean_object* v_r_4014_; 
v_x_228__boxed_4012_ = lean_unbox_usize(v_x_4010_);
lean_dec(v_x_4010_);
v_res_4013_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(v_00_u03b2_4008_, v_x_4009_, v_x_228__boxed_4012_, v_x_4011_);
v_r_4014_ = lean_box(v_res_4013_);
return v_r_4014_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4015_, lean_object* v_keys_4016_, lean_object* v_vals_4017_, lean_object* v_heq_4018_, lean_object* v_i_4019_, lean_object* v_k_4020_){
_start:
{
uint8_t v___x_4021_; 
v___x_4021_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_4016_, v_i_4019_, v_k_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4022_, lean_object* v_keys_4023_, lean_object* v_vals_4024_, lean_object* v_heq_4025_, lean_object* v_i_4026_, lean_object* v_k_4027_){
_start:
{
uint8_t v_res_4028_; lean_object* v_r_4029_; 
v_res_4028_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(v_00_u03b2_4022_, v_keys_4023_, v_vals_4024_, v_heq_4025_, v_i_4026_, v_k_4027_);
lean_dec_ref(v_vals_4024_);
lean_dec_ref(v_keys_4023_);
v_r_4029_ = lean_box(v_res_4028_);
return v_r_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_4030_, lean_object* v_x_4031_, lean_object* v_x_4032_, lean_object* v_x_4033_){
_start:
{
lean_object* v_ks_4034_; lean_object* v_vs_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4059_; 
v_ks_4034_ = lean_ctor_get(v_x_4030_, 0);
v_vs_4035_ = lean_ctor_get(v_x_4030_, 1);
v_isSharedCheck_4059_ = !lean_is_exclusive(v_x_4030_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4037_ = v_x_4030_;
v_isShared_4038_ = v_isSharedCheck_4059_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_vs_4035_);
lean_inc(v_ks_4034_);
lean_dec(v_x_4030_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4059_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4039_; uint8_t v___x_4040_; 
v___x_4039_ = lean_array_get_size(v_ks_4034_);
v___x_4040_ = lean_nat_dec_lt(v_x_4031_, v___x_4039_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4044_; 
lean_dec(v_x_4031_);
v___x_4041_ = lean_array_push(v_ks_4034_, v_x_4032_);
v___x_4042_ = lean_array_push(v_vs_4035_, v_x_4033_);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 1, v___x_4042_);
lean_ctor_set(v___x_4037_, 0, v___x_4041_);
v___x_4044_ = v___x_4037_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4041_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
else
{
lean_object* v_k_x27_4046_; uint8_t v___x_4047_; 
v_k_x27_4046_ = lean_array_fget_borrowed(v_ks_4034_, v_x_4031_);
lean_inc(v_k_x27_4046_);
lean_inc_ref(v_x_4032_);
v___x_4047_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq(v_x_4032_, v_k_x27_4046_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4049_; 
if (v_isShared_4038_ == 0)
{
v___x_4049_ = v___x_4037_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_ks_4034_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_vs_4035_);
v___x_4049_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = lean_unsigned_to_nat(1u);
v___x_4051_ = lean_nat_add(v_x_4031_, v___x_4050_);
lean_dec(v_x_4031_);
v_x_4030_ = v___x_4049_;
v_x_4031_ = v___x_4051_;
goto _start;
}
}
else
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4057_; 
v___x_4054_ = lean_array_fset(v_ks_4034_, v_x_4031_, v_x_4032_);
v___x_4055_ = lean_array_fset(v_vs_4035_, v_x_4031_, v_x_4033_);
lean_dec(v_x_4031_);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 1, v___x_4055_);
lean_ctor_set(v___x_4037_, 0, v___x_4054_);
v___x_4057_ = v___x_4037_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4054_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v___x_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(lean_object* v_n_4060_, lean_object* v_k_4061_, lean_object* v_v_4062_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_unsigned_to_nat(0u);
v___x_4064_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_n_4060_, v___x_4063_, v_k_4061_, v_v_4062_);
return v___x_4064_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(lean_object* v_x_4066_, size_t v_x_4067_, size_t v_x_4068_, lean_object* v_x_4069_, lean_object* v_x_4070_){
_start:
{
if (lean_obj_tag(v_x_4066_) == 0)
{
lean_object* v_es_4071_; size_t v___x_4072_; size_t v___x_4073_; size_t v___x_4074_; size_t v___x_4075_; lean_object* v_j_4076_; lean_object* v___x_4077_; uint8_t v___x_4078_; 
v_es_4071_ = lean_ctor_get(v_x_4066_, 0);
v___x_4072_ = ((size_t)5ULL);
v___x_4073_ = ((size_t)1ULL);
v___x_4074_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__5___redArg___closed__1);
v___x_4075_ = lean_usize_land(v_x_4067_, v___x_4074_);
v_j_4076_ = lean_usize_to_nat(v___x_4075_);
v___x_4077_ = lean_array_get_size(v_es_4071_);
v___x_4078_ = lean_nat_dec_lt(v_j_4076_, v___x_4077_);
if (v___x_4078_ == 0)
{
lean_dec(v_j_4076_);
lean_dec(v_x_4070_);
lean_dec_ref(v_x_4069_);
return v_x_4066_;
}
else
{
lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4115_; 
lean_inc_ref(v_es_4071_);
v_isSharedCheck_4115_ = !lean_is_exclusive(v_x_4066_);
if (v_isSharedCheck_4115_ == 0)
{
lean_object* v_unused_4116_; 
v_unused_4116_ = lean_ctor_get(v_x_4066_, 0);
lean_dec(v_unused_4116_);
v___x_4080_ = v_x_4066_;
v_isShared_4081_ = v_isSharedCheck_4115_;
goto v_resetjp_4079_;
}
else
{
lean_dec(v_x_4066_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4115_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v_v_4082_; lean_object* v___x_4083_; lean_object* v_xs_x27_4084_; lean_object* v___y_4086_; 
v_v_4082_ = lean_array_fget(v_es_4071_, v_j_4076_);
v___x_4083_ = lean_box(0);
v_xs_x27_4084_ = lean_array_fset(v_es_4071_, v_j_4076_, v___x_4083_);
switch(lean_obj_tag(v_v_4082_))
{
case 0:
{
lean_object* v_key_4091_; lean_object* v_val_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4102_; 
v_key_4091_ = lean_ctor_get(v_v_4082_, 0);
v_val_4092_ = lean_ctor_get(v_v_4082_, 1);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_v_4082_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4094_ = v_v_4082_;
v_isShared_4095_ = v_isSharedCheck_4102_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_val_4092_);
lean_inc(v_key_4091_);
lean_dec(v_v_4082_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4102_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
uint8_t v___x_4096_; 
lean_inc(v_key_4091_);
lean_inc_ref(v_x_4069_);
v___x_4096_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instBEqSpecProof_beq(v_x_4069_, v_key_4091_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
lean_del_object(v___x_4094_);
v___x_4097_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4091_, v_val_4092_, v_x_4069_, v_x_4070_);
v___x_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
v___y_4086_ = v___x_4098_;
goto v___jp_4085_;
}
else
{
lean_object* v___x_4100_; 
lean_dec(v_val_4092_);
lean_dec(v_key_4091_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 1, v_x_4070_);
lean_ctor_set(v___x_4094_, 0, v_x_4069_);
v___x_4100_ = v___x_4094_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_x_4069_);
lean_ctor_set(v_reuseFailAlloc_4101_, 1, v_x_4070_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
v___y_4086_ = v___x_4100_;
goto v___jp_4085_;
}
}
}
}
case 1:
{
lean_object* v_node_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4113_; 
v_node_4103_ = lean_ctor_get(v_v_4082_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_v_4082_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4105_ = v_v_4082_;
v_isShared_4106_ = v_isSharedCheck_4113_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_node_4103_);
lean_dec(v_v_4082_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4113_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
size_t v___x_4107_; size_t v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4111_; 
v___x_4107_ = lean_usize_shift_right(v_x_4067_, v___x_4072_);
v___x_4108_ = lean_usize_add(v_x_4068_, v___x_4073_);
v___x_4109_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_node_4103_, v___x_4107_, v___x_4108_, v_x_4069_, v_x_4070_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v___x_4109_);
v___x_4111_ = v___x_4105_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4109_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
v___y_4086_ = v___x_4111_;
goto v___jp_4085_;
}
}
}
default: 
{
lean_object* v___x_4114_; 
v___x_4114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4114_, 0, v_x_4069_);
lean_ctor_set(v___x_4114_, 1, v_x_4070_);
v___y_4086_ = v___x_4114_;
goto v___jp_4085_;
}
}
v___jp_4085_:
{
lean_object* v___x_4087_; lean_object* v___x_4089_; 
v___x_4087_ = lean_array_fset(v_xs_x27_4084_, v_j_4076_, v___y_4086_);
lean_dec(v_j_4076_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___x_4087_);
v___x_4089_ = v___x_4080_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4087_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
else
{
lean_object* v_ks_4117_; lean_object* v_vs_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4138_; 
v_ks_4117_ = lean_ctor_get(v_x_4066_, 0);
v_vs_4118_ = lean_ctor_get(v_x_4066_, 1);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_x_4066_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4120_ = v_x_4066_;
v_isShared_4121_ = v_isSharedCheck_4138_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_vs_4118_);
lean_inc(v_ks_4117_);
lean_dec(v_x_4066_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4138_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_ks_4117_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_vs_4118_);
v___x_4123_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v_newNode_4124_; uint8_t v___y_4126_; size_t v___x_4132_; uint8_t v___x_4133_; 
v_newNode_4124_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v___x_4123_, v_x_4069_, v_x_4070_);
v___x_4132_ = ((size_t)7ULL);
v___x_4133_ = lean_usize_dec_le(v___x_4132_, v_x_4068_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; lean_object* v___x_4135_; uint8_t v___x_4136_; 
v___x_4134_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4124_);
v___x_4135_ = lean_unsigned_to_nat(4u);
v___x_4136_ = lean_nat_dec_lt(v___x_4134_, v___x_4135_);
lean_dec(v___x_4134_);
v___y_4126_ = v___x_4136_;
goto v___jp_4125_;
}
else
{
v___y_4126_ = v___x_4133_;
goto v___jp_4125_;
}
v___jp_4125_:
{
if (v___y_4126_ == 0)
{
lean_object* v_ks_4127_; lean_object* v_vs_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v_ks_4127_ = lean_ctor_get(v_newNode_4124_, 0);
lean_inc_ref(v_ks_4127_);
v_vs_4128_ = lean_ctor_get(v_newNode_4124_, 1);
lean_inc_ref(v_vs_4128_);
lean_dec_ref(v_newNode_4124_);
v___x_4129_ = lean_unsigned_to_nat(0u);
v___x_4130_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0);
v___x_4131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_x_4068_, v_ks_4127_, v_vs_4128_, v___x_4129_, v___x_4130_);
lean_dec_ref(v_vs_4128_);
lean_dec_ref(v_ks_4127_);
return v___x_4131_;
}
else
{
return v_newNode_4124_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(size_t v_depth_4139_, lean_object* v_keys_4140_, lean_object* v_vals_4141_, lean_object* v_i_4142_, lean_object* v_entries_4143_){
_start:
{
lean_object* v___x_4144_; uint8_t v___x_4145_; 
v___x_4144_ = lean_array_get_size(v_keys_4140_);
v___x_4145_ = lean_nat_dec_lt(v_i_4142_, v___x_4144_);
if (v___x_4145_ == 0)
{
lean_dec(v_i_4142_);
return v_entries_4143_;
}
else
{
lean_object* v_k_4146_; lean_object* v_v_4147_; uint64_t v___y_4149_; lean_object* v___y_4161_; lean_object* v_declName_4164_; 
v_k_4146_ = lean_array_fget_borrowed(v_keys_4140_, v_i_4142_);
v_v_4147_ = lean_array_fget_borrowed(v_vals_4141_, v_i_4142_);
v_declName_4164_ = lean_ctor_get(v_k_4146_, 0);
lean_inc(v_declName_4164_);
v___y_4161_ = v_declName_4164_;
goto v___jp_4160_;
v___jp_4148_:
{
size_t v_h_4150_; size_t v___x_4151_; lean_object* v___x_4152_; size_t v___x_4153_; size_t v___x_4154_; size_t v___x_4155_; size_t v_h_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v_h_4150_ = lean_uint64_to_usize(v___y_4149_);
v___x_4151_ = ((size_t)5ULL);
v___x_4152_ = lean_unsigned_to_nat(1u);
v___x_4153_ = ((size_t)1ULL);
v___x_4154_ = lean_usize_sub(v_depth_4139_, v___x_4153_);
v___x_4155_ = lean_usize_mul(v___x_4151_, v___x_4154_);
v_h_4156_ = lean_usize_shift_right(v_h_4150_, v___x_4155_);
v___x_4157_ = lean_nat_add(v_i_4142_, v___x_4152_);
lean_dec(v_i_4142_);
lean_inc(v_v_4147_);
lean_inc(v_k_4146_);
v___x_4158_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_entries_4143_, v_h_4156_, v_depth_4139_, v_k_4146_, v_v_4147_);
v_i_4142_ = v___x_4157_;
v_entries_4143_ = v___x_4158_;
goto _start;
}
v___jp_4160_:
{
if (lean_obj_tag(v___y_4161_) == 0)
{
uint64_t v___x_4162_; 
v___x_4162_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_4149_ = v___x_4162_;
goto v___jp_4148_;
}
else
{
uint64_t v_hash_4163_; 
v_hash_4163_ = lean_ctor_get_uint64(v___y_4161_, sizeof(void*)*2);
lean_dec(v___y_4161_);
v___y_4149_ = v_hash_4163_;
goto v___jp_4148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_4165_, lean_object* v_keys_4166_, lean_object* v_vals_4167_, lean_object* v_i_4168_, lean_object* v_entries_4169_){
_start:
{
size_t v_depth_boxed_4170_; lean_object* v_res_4171_; 
v_depth_boxed_4170_ = lean_unbox_usize(v_depth_4165_);
lean_dec(v_depth_4165_);
v_res_4171_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_boxed_4170_, v_keys_4166_, v_vals_4167_, v_i_4168_, v_entries_4169_);
lean_dec_ref(v_vals_4167_);
lean_dec_ref(v_keys_4166_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_4172_, lean_object* v_x_4173_, lean_object* v_x_4174_, lean_object* v_x_4175_, lean_object* v_x_4176_){
_start:
{
size_t v_x_400__boxed_4177_; size_t v_x_401__boxed_4178_; lean_object* v_res_4179_; 
v_x_400__boxed_4177_ = lean_unbox_usize(v_x_4173_);
lean_dec(v_x_4173_);
v_x_401__boxed_4178_ = lean_unbox_usize(v_x_4174_);
lean_dec(v_x_4174_);
v_res_4179_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_4172_, v_x_400__boxed_4177_, v_x_401__boxed_4178_, v_x_4175_, v_x_4176_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0___redArg(lean_object* v_x_4180_, lean_object* v_x_4181_, lean_object* v_x_4182_){
_start:
{
uint64_t v___y_4184_; lean_object* v___y_4189_; lean_object* v_declName_4192_; 
v_declName_4192_ = lean_ctor_get(v_x_4181_, 0);
lean_inc(v_declName_4192_);
v___y_4189_ = v_declName_4192_;
goto v___jp_4188_;
v___jp_4183_:
{
size_t v___x_4185_; size_t v___x_4186_; lean_object* v___x_4187_; 
v___x_4185_ = lean_uint64_to_usize(v___y_4184_);
v___x_4186_ = ((size_t)1ULL);
v___x_4187_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_4180_, v___x_4185_, v___x_4186_, v_x_4181_, v_x_4182_);
return v___x_4187_;
}
v___jp_4188_:
{
if (lean_obj_tag(v___y_4189_) == 0)
{
uint64_t v___x_4190_; 
v___x_4190_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
v___y_4184_ = v___x_4190_;
goto v___jp_4183_;
}
else
{
uint64_t v_hash_4191_; 
v_hash_4191_ = lean_ctor_get_uint64(v___y_4189_, sizeof(void*)*2);
lean_dec(v___y_4189_);
v___y_4184_ = v_hash_4191_;
goto v___jp_4183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase(lean_object* v_d_4193_, lean_object* v_thmId_4194_){
_start:
{
lean_object* v_specs_4195_; lean_object* v_erased_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4205_; 
v_specs_4195_ = lean_ctor_get(v_d_4193_, 0);
v_erased_4196_ = lean_ctor_get(v_d_4193_, 1);
v_isSharedCheck_4205_ = !lean_is_exclusive(v_d_4193_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4198_ = v_d_4193_;
v_isShared_4199_ = v_isSharedCheck_4205_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_erased_4196_);
lean_inc(v_specs_4195_);
lean_dec(v_d_4193_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4205_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4203_; 
v___x_4200_ = lean_box(0);
v___x_4201_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_erased_4196_, v_thmId_4194_, v___x_4200_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 1, v___x_4201_);
v___x_4203_ = v___x_4198_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_specs_4195_);
lean_ctor_set(v_reuseFailAlloc_4204_, 1, v___x_4201_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0(lean_object* v_00_u03b2_4206_, lean_object* v_x_4207_, lean_object* v_x_4208_, lean_object* v_x_4209_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_x_4207_, v_x_4208_, v_x_4209_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0(lean_object* v_00_u03b2_4211_, lean_object* v_x_4212_, size_t v_x_4213_, size_t v_x_4214_, lean_object* v_x_4215_, lean_object* v_x_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_4212_, v_x_4213_, v_x_4214_, v_x_4215_, v_x_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4218_, lean_object* v_x_4219_, lean_object* v_x_4220_, lean_object* v_x_4221_, lean_object* v_x_4222_, lean_object* v_x_4223_){
_start:
{
size_t v_x_618__boxed_4224_; size_t v_x_619__boxed_4225_; lean_object* v_res_4226_; 
v_x_618__boxed_4224_ = lean_unbox_usize(v_x_4220_);
lean_dec(v_x_4220_);
v_x_619__boxed_4225_ = lean_unbox_usize(v_x_4221_);
lean_dec(v_x_4221_);
v_res_4226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0(v_00_u03b2_4218_, v_x_4219_, v_x_618__boxed_4224_, v_x_619__boxed_4225_, v_x_4222_, v_x_4223_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4227_, lean_object* v_n_4228_, lean_object* v_k_4229_, lean_object* v_v_4230_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v_n_4228_, v_k_4229_, v_v_4230_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_4232_, size_t v_depth_4233_, lean_object* v_keys_4234_, lean_object* v_vals_4235_, lean_object* v_heq_4236_, lean_object* v_i_4237_, lean_object* v_entries_4238_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_4233_, v_keys_4234_, v_vals_4235_, v_i_4237_, v_entries_4238_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4240_, lean_object* v_depth_4241_, lean_object* v_keys_4242_, lean_object* v_vals_4243_, lean_object* v_heq_4244_, lean_object* v_i_4245_, lean_object* v_entries_4246_){
_start:
{
size_t v_depth_boxed_4247_; lean_object* v_res_4248_; 
v_depth_boxed_4247_ = lean_unbox_usize(v_depth_4241_);
lean_dec(v_depth_4241_);
v_res_4248_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(v_00_u03b2_4240_, v_depth_boxed_4247_, v_keys_4242_, v_vals_4243_, v_heq_4244_, v_i_4245_, v_entries_4246_);
lean_dec_ref(v_vals_4243_);
lean_dec_ref(v_keys_4242_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4249_, lean_object* v_x_4250_, lean_object* v_x_4251_, lean_object* v_x_4252_, lean_object* v_x_4253_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_x_4250_, v_x_4251_, v_x_4252_, v_x_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__2(lean_object* v___x_4255_, size_t v_sz_4256_, size_t v_i_4257_, lean_object* v_bs_4258_){
_start:
{
uint8_t v___x_4259_; 
v___x_4259_ = lean_usize_dec_lt(v_i_4257_, v_sz_4256_);
if (v___x_4259_ == 0)
{
return v_bs_4258_;
}
else
{
lean_object* v_v_4260_; lean_object* v___x_4261_; lean_object* v_bs_x27_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; size_t v___x_4265_; size_t v___x_4266_; lean_object* v___x_4267_; 
v_v_4260_ = lean_array_uget(v_bs_4258_, v_i_4257_);
v___x_4261_ = lean_unsigned_to_nat(0u);
v_bs_x27_4262_ = lean_array_uset(v_bs_4258_, v_i_4257_, v___x_4261_);
v___x_4263_ = l_Lean_instInhabitedExpr;
v___x_4264_ = lean_array_get_borrowed(v___x_4263_, v___x_4255_, v_v_4260_);
lean_dec(v_v_4260_);
v___x_4265_ = ((size_t)1ULL);
v___x_4266_ = lean_usize_add(v_i_4257_, v___x_4265_);
lean_inc(v___x_4264_);
v___x_4267_ = lean_array_uset(v_bs_x27_4262_, v_i_4257_, v___x_4264_);
v_i_4257_ = v___x_4266_;
v_bs_4258_ = v___x_4267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__2___boxed(lean_object* v___x_4269_, lean_object* v_sz_4270_, lean_object* v_i_4271_, lean_object* v_bs_4272_){
_start:
{
size_t v_sz_boxed_4273_; size_t v_i_boxed_4274_; lean_object* v_res_4275_; 
v_sz_boxed_4273_ = lean_unbox_usize(v_sz_4270_);
lean_dec(v_sz_4270_);
v_i_boxed_4274_ = lean_unbox_usize(v_i_4271_);
lean_dec(v_i_4271_);
v_res_4275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__2(v___x_4269_, v_sz_boxed_4273_, v_i_boxed_4274_, v_bs_4272_);
lean_dec_ref(v___x_4269_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1(size_t v_sz_4279_, size_t v_i_4280_, lean_object* v_bs_4281_){
_start:
{
uint8_t v___x_4282_; 
v___x_4282_ = lean_usize_dec_lt(v_i_4280_, v_sz_4279_);
if (v___x_4282_ == 0)
{
return v_bs_4281_;
}
else
{
lean_object* v_v_4283_; lean_object* v___x_4284_; lean_object* v_bs_x27_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; size_t v___x_4289_; size_t v___x_4290_; lean_object* v___x_4291_; 
v_v_4283_ = lean_array_uget(v_bs_4281_, v_i_4280_);
v___x_4284_ = lean_unsigned_to_nat(0u);
v_bs_x27_4285_ = lean_array_uset(v_bs_4281_, v_i_4280_, v___x_4284_);
v___x_4286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1___closed__1));
v___x_4287_ = l_Lean_Name_num___override(v___x_4286_, v_v_4283_);
v___x_4288_ = l_Lean_mkFVar(v___x_4287_);
v___x_4289_ = ((size_t)1ULL);
v___x_4290_ = lean_usize_add(v_i_4280_, v___x_4289_);
v___x_4291_ = lean_array_uset(v_bs_x27_4285_, v_i_4280_, v___x_4288_);
v_i_4280_ = v___x_4290_;
v_bs_4281_ = v___x_4291_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1___boxed(lean_object* v_sz_4293_, lean_object* v_i_4294_, lean_object* v_bs_4295_){
_start:
{
size_t v_sz_boxed_4296_; size_t v_i_boxed_4297_; lean_object* v_res_4298_; 
v_sz_boxed_4296_ = lean_unbox_usize(v_sz_4293_);
lean_dec(v_sz_4293_);
v_i_boxed_4297_ = lean_unbox_usize(v_i_4294_);
lean_dec(v_i_4294_);
v_res_4298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1(v_sz_boxed_4296_, v_i_boxed_4297_, v_bs_4295_);
return v_res_4298_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__5(lean_object* v_as_4299_, size_t v_i_4300_, size_t v_stop_4301_){
_start:
{
uint8_t v___x_4302_; 
v___x_4302_ = lean_usize_dec_eq(v_i_4300_, v_stop_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4303_ = lean_array_uget_borrowed(v_as_4299_, v_i_4300_);
v___x_4304_ = lean_unbox(v___x_4303_);
if (v___x_4304_ == 0)
{
size_t v___x_4305_; size_t v___x_4306_; 
v___x_4305_ = ((size_t)1ULL);
v___x_4306_ = lean_usize_add(v_i_4300_, v___x_4305_);
v_i_4300_ = v___x_4306_;
goto _start;
}
else
{
uint8_t v___x_4308_; 
v___x_4308_ = lean_unbox(v___x_4303_);
return v___x_4308_;
}
}
else
{
uint8_t v___x_4309_; 
v___x_4309_ = 0;
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__5___boxed(lean_object* v_as_4310_, lean_object* v_i_4311_, lean_object* v_stop_4312_){
_start:
{
size_t v_i_boxed_4313_; size_t v_stop_boxed_4314_; uint8_t v_res_4315_; lean_object* v_r_4316_; 
v_i_boxed_4313_ = lean_unbox_usize(v_i_4311_);
lean_dec(v_i_4311_);
v_stop_boxed_4314_ = lean_unbox_usize(v_stop_4312_);
lean_dec(v_stop_4312_);
v_res_4315_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__5(v_as_4310_, v_i_boxed_4313_, v_stop_boxed_4314_);
lean_dec_ref(v_as_4310_);
v_r_4316_ = lean_box(v_res_4315_);
return v_r_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__6(lean_object* v_val_4317_, size_t v_sz_4318_, size_t v_i_4319_, lean_object* v_bs_4320_){
_start:
{
uint8_t v___x_4321_; 
v___x_4321_ = lean_usize_dec_lt(v_i_4319_, v_sz_4318_);
if (v___x_4321_ == 0)
{
return v_bs_4320_;
}
else
{
lean_object* v_v_4322_; lean_object* v___x_4323_; lean_object* v_bs_x27_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; size_t v___x_4327_; size_t v___x_4328_; lean_object* v___x_4329_; 
v_v_4322_ = lean_array_uget(v_bs_4320_, v_i_4319_);
v___x_4323_ = lean_unsigned_to_nat(0u);
v_bs_x27_4324_ = lean_array_uset(v_bs_4320_, v_i_4319_, v___x_4323_);
v___x_4325_ = l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default;
v___x_4326_ = lean_array_get_borrowed(v___x_4325_, v_val_4317_, v_v_4322_);
lean_dec(v_v_4322_);
v___x_4327_ = ((size_t)1ULL);
v___x_4328_ = lean_usize_add(v_i_4319_, v___x_4327_);
lean_inc(v___x_4326_);
v___x_4329_ = lean_array_uset(v_bs_x27_4324_, v_i_4319_, v___x_4326_);
v_i_4319_ = v___x_4328_;
v_bs_4320_ = v___x_4329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__6___boxed(lean_object* v_val_4331_, lean_object* v_sz_4332_, lean_object* v_i_4333_, lean_object* v_bs_4334_){
_start:
{
size_t v_sz_boxed_4335_; size_t v_i_boxed_4336_; lean_object* v_res_4337_; 
v_sz_boxed_4335_ = lean_unbox_usize(v_sz_4332_);
lean_dec(v_sz_4332_);
v_i_boxed_4336_ = lean_unbox_usize(v_i_4333_);
lean_dec(v_i_4333_);
v_res_4337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__6(v_val_4331_, v_sz_boxed_4335_, v_i_boxed_4336_, v_bs_4334_);
lean_dec_ref(v_val_4331_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11___redArg(lean_object* v_upperBound_4338_, lean_object* v_p_4339_, lean_object* v_n_4340_, lean_object* v_a_4341_, lean_object* v_b_4342_){
_start:
{
lean_object* v_a_4344_; uint8_t v___x_4348_; 
v___x_4348_ = lean_nat_dec_lt(v_a_4341_, v_upperBound_4338_);
if (v___x_4348_ == 0)
{
lean_dec(v_a_4341_);
return v_b_4342_;
}
else
{
lean_object* v_pattern_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
v_pattern_4349_ = lean_ctor_get(v_p_4339_, 3);
v___x_4350_ = lean_unsigned_to_nat(1u);
v___x_4351_ = lean_nat_sub(v_n_4340_, v___x_4350_);
v___x_4352_ = lean_nat_sub(v___x_4351_, v_a_4341_);
lean_dec(v___x_4351_);
v___x_4353_ = lean_expr_has_loose_bvar(v_pattern_4349_, v___x_4352_);
lean_dec(v___x_4352_);
if (v___x_4353_ == 0)
{
v_a_4344_ = v_b_4342_;
goto v___jp_4343_;
}
else
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4354_ = lean_box(v___x_4353_);
v___x_4355_ = lean_array_set(v_b_4342_, v_a_4341_, v___x_4354_);
v_a_4344_ = v___x_4355_;
goto v___jp_4343_;
}
}
v___jp_4343_:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4345_ = lean_unsigned_to_nat(1u);
v___x_4346_ = lean_nat_add(v_a_4341_, v___x_4345_);
lean_dec(v_a_4341_);
v_a_4341_ = v___x_4346_;
v_b_4342_ = v_a_4344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11___redArg___boxed(lean_object* v_upperBound_4356_, lean_object* v_p_4357_, lean_object* v_n_4358_, lean_object* v_a_4359_, lean_object* v_b_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11___redArg(v_upperBound_4356_, v_p_4357_, v_n_4358_, v_a_4359_, v_b_4360_);
lean_dec(v_n_4358_);
lean_dec_ref(v_p_4357_);
lean_dec(v_upperBound_4356_);
return v_res_4361_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__0(lean_object* v_as_4362_, size_t v_i_4363_, size_t v_stop_4364_){
_start:
{
uint8_t v___x_4365_; 
v___x_4365_ = lean_usize_dec_eq(v_i_4363_, v_stop_4364_);
if (v___x_4365_ == 0)
{
uint8_t v___x_4366_; lean_object* v___x_4367_; uint8_t v___x_4368_; 
v___x_4366_ = 1;
v___x_4367_ = lean_array_uget_borrowed(v_as_4362_, v_i_4363_);
v___x_4368_ = lean_unbox(v___x_4367_);
if (v___x_4368_ == 0)
{
return v___x_4366_;
}
else
{
if (v___x_4365_ == 0)
{
size_t v___x_4369_; size_t v___x_4370_; 
v___x_4369_ = ((size_t)1ULL);
v___x_4370_ = lean_usize_add(v_i_4363_, v___x_4369_);
v_i_4363_ = v___x_4370_;
goto _start;
}
else
{
return v___x_4366_;
}
}
}
else
{
uint8_t v___x_4372_; 
v___x_4372_ = 0;
return v___x_4372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__0___boxed(lean_object* v_as_4373_, lean_object* v_i_4374_, lean_object* v_stop_4375_){
_start:
{
size_t v_i_boxed_4376_; size_t v_stop_boxed_4377_; uint8_t v_res_4378_; lean_object* v_r_4379_; 
v_i_boxed_4376_ = lean_unbox_usize(v_i_4374_);
lean_dec(v_i_4374_);
v_stop_boxed_4377_ = lean_unbox_usize(v_stop_4375_);
lean_dec(v_stop_4375_);
v_res_4378_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__0(v_as_4373_, v_i_boxed_4376_, v_stop_boxed_4377_);
lean_dec_ref(v_as_4373_);
v_r_4379_ = lean_box(v_res_4378_);
return v_r_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__8(lean_object* v___y_4380_, lean_object* v_as_4381_, size_t v_i_4382_, size_t v_stop_4383_, lean_object* v_b_4384_){
_start:
{
lean_object* v___y_4386_; uint8_t v___x_4390_; 
v___x_4390_ = lean_usize_dec_eq(v_i_4382_, v_stop_4383_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; uint8_t v___x_4394_; 
v___x_4391_ = lean_array_uget_borrowed(v_as_4381_, v_i_4382_);
v___x_4392_ = lean_box(v___x_4390_);
v___x_4393_ = lean_array_get(v___x_4392_, v___y_4380_, v___x_4391_);
lean_dec(v___x_4392_);
v___x_4394_ = lean_unbox(v___x_4393_);
lean_dec(v___x_4393_);
if (v___x_4394_ == 0)
{
v___y_4386_ = v_b_4384_;
goto v___jp_4385_;
}
else
{
lean_object* v___x_4395_; 
lean_inc(v___x_4391_);
v___x_4395_ = lean_array_push(v_b_4384_, v___x_4391_);
v___y_4386_ = v___x_4395_;
goto v___jp_4385_;
}
}
else
{
return v_b_4384_;
}
v___jp_4385_:
{
size_t v___x_4387_; size_t v___x_4388_; 
v___x_4387_ = ((size_t)1ULL);
v___x_4388_ = lean_usize_add(v_i_4382_, v___x_4387_);
v_i_4382_ = v___x_4388_;
v_b_4384_ = v___y_4386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__8___boxed(lean_object* v___y_4396_, lean_object* v_as_4397_, lean_object* v_i_4398_, lean_object* v_stop_4399_, lean_object* v_b_4400_){
_start:
{
size_t v_i_boxed_4401_; size_t v_stop_boxed_4402_; lean_object* v_res_4403_; 
v_i_boxed_4401_ = lean_unbox_usize(v_i_4398_);
lean_dec(v_i_4398_);
v_stop_boxed_4402_ = lean_unbox_usize(v_stop_4399_);
lean_dec(v_stop_4399_);
v_res_4403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__8(v___y_4396_, v_as_4397_, v_i_boxed_4401_, v_stop_boxed_4402_, v_b_4400_);
lean_dec_ref(v_as_4397_);
lean_dec_ref(v___y_4396_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3___redArg(lean_object* v___x_4404_, lean_object* v___x_4405_, lean_object* v___x_4406_, lean_object* v_as_4407_, lean_object* v_i_4408_, lean_object* v_j_4409_, lean_object* v_bs_4410_){
_start:
{
lean_object* v_zero_4411_; uint8_t v_isZero_4412_; 
v_zero_4411_ = lean_unsigned_to_nat(0u);
v_isZero_4412_ = lean_nat_dec_eq(v_i_4408_, v_zero_4411_);
if (v_isZero_4412_ == 1)
{
lean_dec(v_j_4409_);
lean_dec(v_i_4408_);
return v_bs_4410_;
}
else
{
lean_object* v_one_4413_; lean_object* v_n_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v_one_4413_ = lean_unsigned_to_nat(1u);
v_n_4414_ = lean_nat_sub(v_i_4408_, v_one_4413_);
lean_dec(v_i_4408_);
v___x_4415_ = lean_array_fget_borrowed(v_as_4407_, v_j_4409_);
v___x_4416_ = l_Lean_instInhabitedExpr;
v___x_4417_ = lean_array_get_borrowed(v___x_4416_, v___x_4404_, v___x_4415_);
lean_inc(v___x_4415_);
v___x_4418_ = l_Array_extract___redArg(v___x_4405_, v_zero_4411_, v___x_4415_);
v___x_4419_ = lean_expr_instantiate_rev(v___x_4417_, v___x_4418_);
lean_dec_ref(v___x_4418_);
lean_inc(v_j_4409_);
v___x_4420_ = l_Array_extract___redArg(v___x_4406_, v_zero_4411_, v_j_4409_);
v___x_4421_ = lean_expr_abstract(v___x_4419_, v___x_4420_);
lean_dec_ref(v___x_4420_);
lean_dec_ref(v___x_4419_);
v___x_4422_ = lean_nat_add(v_j_4409_, v_one_4413_);
lean_dec(v_j_4409_);
v___x_4423_ = lean_array_push(v_bs_4410_, v___x_4421_);
v_i_4408_ = v_n_4414_;
v_j_4409_ = v___x_4422_;
v_bs_4410_ = v___x_4423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3___redArg___boxed(lean_object* v___x_4425_, lean_object* v___x_4426_, lean_object* v___x_4427_, lean_object* v_as_4428_, lean_object* v_i_4429_, lean_object* v_j_4430_, lean_object* v_bs_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3___redArg(v___x_4425_, v___x_4426_, v___x_4427_, v_as_4428_, v_i_4429_, v_j_4430_, v_bs_4431_);
lean_dec_ref(v_as_4428_);
lean_dec_ref(v___x_4427_);
lean_dec_ref(v___x_4426_);
lean_dec_ref(v___x_4425_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9___redArg(lean_object* v_upperBound_4433_, lean_object* v___x_4434_, lean_object* v___x_4435_, uint8_t v___x_4436_, lean_object* v_a_4437_, lean_object* v_b_4438_){
_start:
{
uint8_t v___x_4439_; 
v___x_4439_ = lean_nat_dec_lt(v_a_4437_, v_upperBound_4433_);
if (v___x_4439_ == 0)
{
lean_dec(v_a_4437_);
return v_b_4438_;
}
else
{
lean_object* v___x_4440_; lean_object* v_a_4442_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; uint8_t v___x_4449_; 
v___x_4440_ = lean_unsigned_to_nat(1u);
v___x_4445_ = l_Lean_instInhabitedExpr;
v___x_4446_ = lean_array_get_borrowed(v___x_4445_, v___x_4434_, v___x_4435_);
v___x_4447_ = lean_nat_sub(v___x_4435_, v___x_4440_);
v___x_4448_ = lean_nat_sub(v___x_4447_, v_a_4437_);
lean_dec(v___x_4447_);
v___x_4449_ = lean_expr_has_loose_bvar(v___x_4446_, v___x_4448_);
lean_dec(v___x_4448_);
if (v___x_4449_ == 0)
{
v_a_4442_ = v_b_4438_;
goto v___jp_4441_;
}
else
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4450_ = lean_box(v___x_4436_);
v___x_4451_ = lean_array_set(v_b_4438_, v_a_4437_, v___x_4450_);
v_a_4442_ = v___x_4451_;
goto v___jp_4441_;
}
v___jp_4441_:
{
lean_object* v___x_4443_; 
v___x_4443_ = lean_nat_add(v_a_4437_, v___x_4440_);
lean_dec(v_a_4437_);
v_a_4437_ = v___x_4443_;
v_b_4438_ = v_a_4442_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9___redArg___boxed(lean_object* v_upperBound_4452_, lean_object* v___x_4453_, lean_object* v___x_4454_, lean_object* v___x_4455_, lean_object* v_a_4456_, lean_object* v_b_4457_){
_start:
{
uint8_t v___x_5124__boxed_4458_; lean_object* v_res_4459_; 
v___x_5124__boxed_4458_ = lean_unbox(v___x_4455_);
v_res_4459_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9___redArg(v_upperBound_4452_, v___x_4453_, v___x_4454_, v___x_5124__boxed_4458_, v_a_4456_, v_b_4457_);
lean_dec(v___x_4454_);
lean_dec_ref(v___x_4453_);
lean_dec(v_upperBound_4452_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10___redArg(lean_object* v_upperBound_4460_, lean_object* v_n_4461_, lean_object* v___x_4462_, lean_object* v_a_4463_, lean_object* v_b_4464_){
_start:
{
lean_object* v_a_4466_; uint8_t v___x_4470_; 
v___x_4470_ = lean_nat_dec_lt(v_a_4463_, v_upperBound_4460_);
if (v___x_4470_ == 0)
{
lean_dec(v_a_4463_);
return v_b_4464_;
}
else
{
uint8_t v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; uint8_t v___x_4477_; 
v___x_4471_ = 0;
v___x_4472_ = lean_unsigned_to_nat(1u);
v___x_4473_ = lean_nat_sub(v_n_4461_, v___x_4472_);
v___x_4474_ = lean_nat_sub(v___x_4473_, v_a_4463_);
lean_dec(v___x_4473_);
v___x_4475_ = lean_box(v___x_4471_);
v___x_4476_ = lean_array_get(v___x_4475_, v_b_4464_, v___x_4474_);
lean_dec(v___x_4475_);
v___x_4477_ = lean_unbox(v___x_4476_);
if (v___x_4477_ == 0)
{
lean_dec(v___x_4476_);
lean_dec(v___x_4474_);
v_a_4466_ = v_b_4464_;
goto v___jp_4465_;
}
else
{
lean_object* v___x_4478_; uint8_t v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = lean_unsigned_to_nat(0u);
v___x_4479_ = lean_unbox(v___x_4476_);
lean_dec(v___x_4476_);
v___x_4480_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9___redArg(v___x_4474_, v___x_4462_, v___x_4474_, v___x_4479_, v___x_4478_, v_b_4464_);
lean_dec(v___x_4474_);
v_a_4466_ = v___x_4480_;
goto v___jp_4465_;
}
}
v___jp_4465_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = lean_unsigned_to_nat(1u);
v___x_4468_ = lean_nat_add(v_a_4463_, v___x_4467_);
lean_dec(v_a_4463_);
v_a_4463_ = v___x_4468_;
v_b_4464_ = v_a_4466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10___redArg___boxed(lean_object* v_upperBound_4481_, lean_object* v_n_4482_, lean_object* v___x_4483_, lean_object* v_a_4484_, lean_object* v_b_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10___redArg(v_upperBound_4481_, v_n_4482_, v___x_4483_, v_a_4484_, v_b_4485_);
lean_dec_ref(v___x_4483_);
lean_dec(v_n_4482_);
lean_dec(v_upperBound_4481_);
return v_res_4486_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__7(uint8_t v___x_4487_, lean_object* v_as_4488_, size_t v_i_4489_, size_t v_stop_4490_){
_start:
{
uint8_t v___x_4491_; 
v___x_4491_ = lean_usize_dec_eq(v_i_4489_, v_stop_4490_);
if (v___x_4491_ == 0)
{
lean_object* v___x_4492_; uint8_t v_isProof_4493_; uint8_t v_isInstance_4494_; uint8_t v___x_4495_; uint8_t v___y_4497_; 
v___x_4492_ = lean_array_uget_borrowed(v_as_4488_, v_i_4489_);
v_isProof_4493_ = lean_ctor_get_uint8(v___x_4492_, 0);
v_isInstance_4494_ = lean_ctor_get_uint8(v___x_4492_, 1);
v___x_4495_ = 1;
if (v_isProof_4493_ == 0)
{
v___y_4497_ = v_isInstance_4494_;
goto v___jp_4496_;
}
else
{
v___y_4497_ = v___x_4487_;
goto v___jp_4496_;
}
v___jp_4496_:
{
if (v___y_4497_ == 0)
{
size_t v___x_4498_; size_t v___x_4499_; 
v___x_4498_ = ((size_t)1ULL);
v___x_4499_ = lean_usize_add(v_i_4489_, v___x_4498_);
v_i_4489_ = v___x_4499_;
goto _start;
}
else
{
return v___x_4495_;
}
}
}
else
{
uint8_t v___x_4501_; 
v___x_4501_ = 0;
return v___x_4501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__7___boxed(lean_object* v___x_4502_, lean_object* v_as_4503_, lean_object* v_i_4504_, lean_object* v_stop_4505_){
_start:
{
uint8_t v___x_5197__boxed_4506_; size_t v_i_boxed_4507_; size_t v_stop_boxed_4508_; uint8_t v_res_4509_; lean_object* v_r_4510_; 
v___x_5197__boxed_4506_ = lean_unbox(v___x_4502_);
v_i_boxed_4507_ = lean_unbox_usize(v_i_4504_);
lean_dec(v_i_4504_);
v_stop_boxed_4508_ = lean_unbox_usize(v_stop_4505_);
lean_dec(v_stop_4505_);
v_res_4509_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__7(v___x_5197__boxed_4506_, v_as_4503_, v_i_boxed_4507_, v_stop_boxed_4508_);
lean_dec_ref(v_as_4503_);
v_r_4510_ = lean_box(v_res_4509_);
return v_r_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__4(lean_object* v_val_4511_, size_t v_sz_4512_, size_t v_i_4513_, lean_object* v_bs_4514_){
_start:
{
uint8_t v___x_4515_; 
v___x_4515_ = lean_usize_dec_lt(v_i_4513_, v_sz_4512_);
if (v___x_4515_ == 0)
{
return v_bs_4514_;
}
else
{
uint8_t v___x_4516_; lean_object* v_v_4517_; lean_object* v___x_4518_; lean_object* v_bs_x27_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; size_t v___x_4522_; size_t v___x_4523_; lean_object* v___x_4524_; 
v___x_4516_ = 0;
v_v_4517_ = lean_array_uget(v_bs_4514_, v_i_4513_);
v___x_4518_ = lean_unsigned_to_nat(0u);
v_bs_x27_4519_ = lean_array_uset(v_bs_4514_, v_i_4513_, v___x_4518_);
v___x_4520_ = lean_box(v___x_4516_);
v___x_4521_ = lean_array_get(v___x_4520_, v_val_4511_, v_v_4517_);
lean_dec(v_v_4517_);
lean_dec(v___x_4520_);
v___x_4522_ = ((size_t)1ULL);
v___x_4523_ = lean_usize_add(v_i_4513_, v___x_4522_);
v___x_4524_ = lean_array_uset(v_bs_x27_4519_, v_i_4513_, v___x_4521_);
v_i_4513_ = v___x_4523_;
v_bs_4514_ = v___x_4524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__4___boxed(lean_object* v_val_4526_, lean_object* v_sz_4527_, lean_object* v_i_4528_, lean_object* v_bs_4529_){
_start:
{
size_t v_sz_boxed_4530_; size_t v_i_boxed_4531_; lean_object* v_res_4532_; 
v_sz_boxed_4530_ = lean_unbox_usize(v_sz_4527_);
lean_dec(v_sz_4527_);
v_i_boxed_4531_ = lean_unbox_usize(v_i_4528_);
lean_dec(v_i_4528_);
v_res_4532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__4(v_val_4526_, v_sz_boxed_4530_, v_i_boxed_4531_, v_bs_4529_);
lean_dec_ref(v_val_4526_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern(lean_object* v_p_4535_){
_start:
{
lean_object* v_levelParams_4536_; lean_object* v_varTypes_4537_; lean_object* v_varInfos_x3f_4538_; lean_object* v_pattern_4539_; lean_object* v_fnInfos_4540_; lean_object* v_checkTypeMask_x3f_4541_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v_n_4548_; uint8_t v___x_4549_; lean_object* v___x_4550_; lean_object* v_used_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; uint8_t v___x_4556_; 
v_levelParams_4536_ = lean_ctor_get(v_p_4535_, 0);
v_varTypes_4537_ = lean_ctor_get(v_p_4535_, 1);
v_varInfos_x3f_4538_ = lean_ctor_get(v_p_4535_, 2);
lean_inc(v_varInfos_x3f_4538_);
v_pattern_4539_ = lean_ctor_get(v_p_4535_, 3);
v_fnInfos_4540_ = lean_ctor_get(v_p_4535_, 4);
v_checkTypeMask_x3f_4541_ = lean_ctor_get(v_p_4535_, 5);
lean_inc(v_checkTypeMask_x3f_4541_);
v_n_4548_ = lean_array_get_size(v_varTypes_4537_);
v___x_4549_ = 0;
v___x_4550_ = lean_box(v___x_4549_);
v_used_4551_ = lean_mk_array(v_n_4548_, v___x_4550_);
v___x_4552_ = lean_unsigned_to_nat(0u);
v___x_4553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11___redArg(v_n_4548_, v_p_4535_, v_n_4548_, v___x_4552_, v_used_4551_);
v___x_4554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10___redArg(v_n_4548_, v_n_4548_, v_varTypes_4537_, v___x_4552_, v___x_4553_);
v___x_4555_ = lean_array_get_size(v___x_4554_);
v___x_4556_ = lean_nat_dec_lt(v___x_4552_, v___x_4555_);
if (v___x_4556_ == 0)
{
lean_dec_ref(v___x_4554_);
lean_dec(v_checkTypeMask_x3f_4541_);
lean_dec(v_varInfos_x3f_4538_);
return v_p_4535_;
}
else
{
if (v___x_4556_ == 0)
{
lean_dec_ref(v___x_4554_);
lean_dec(v_checkTypeMask_x3f_4541_);
lean_dec(v_varInfos_x3f_4538_);
return v_p_4535_;
}
else
{
size_t v___x_4557_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; size_t v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; size_t v___y_4583_; size_t v___x_4585_; uint8_t v___x_4586_; 
v___x_4557_ = ((size_t)0ULL);
v___x_4585_ = lean_usize_of_nat(v___x_4555_);
v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__0(v___x_4554_, v___x_4557_, v___x_4585_);
if (v___x_4586_ == 0)
{
lean_dec_ref(v___x_4554_);
lean_dec(v_checkTypeMask_x3f_4541_);
lean_dec(v_varInfos_x3f_4538_);
return v_p_4535_;
}
else
{
lean_object* v___x_4587_; lean_object* v___y_4589_; lean_object* v___x_4612_; lean_object* v___x_4613_; uint8_t v___x_4614_; 
lean_inc(v_fnInfos_4540_);
lean_inc_ref(v_pattern_4539_);
lean_inc_ref(v_varTypes_4537_);
lean_inc(v_levelParams_4536_);
lean_dec_ref(v_p_4535_);
v___x_4587_ = l_Array_range(v_n_4548_);
v___x_4612_ = lean_array_get_size(v___x_4587_);
v___x_4613_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern___closed__0));
v___x_4614_ = lean_nat_dec_lt(v___x_4552_, v___x_4612_);
if (v___x_4614_ == 0)
{
lean_dec_ref(v___x_4554_);
v___y_4589_ = v___x_4613_;
goto v___jp_4588_;
}
else
{
uint8_t v___x_4615_; 
v___x_4615_ = lean_nat_dec_le(v___x_4612_, v___x_4612_);
if (v___x_4615_ == 0)
{
if (v___x_4614_ == 0)
{
lean_dec_ref(v___x_4554_);
v___y_4589_ = v___x_4613_;
goto v___jp_4588_;
}
else
{
size_t v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = lean_usize_of_nat(v___x_4612_);
v___x_4617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__8(v___x_4554_, v___x_4587_, v___x_4557_, v___x_4616_, v___x_4613_);
lean_dec_ref(v___x_4554_);
v___y_4589_ = v___x_4617_;
goto v___jp_4588_;
}
}
else
{
size_t v___x_4618_; lean_object* v___x_4619_; 
v___x_4618_ = lean_usize_of_nat(v___x_4612_);
v___x_4619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__8(v___x_4554_, v___x_4587_, v___x_4557_, v___x_4618_, v___x_4613_);
lean_dec_ref(v___x_4554_);
v___y_4589_ = v___x_4619_;
goto v___jp_4588_;
}
}
v___jp_4588_:
{
size_t v_sz_4590_; lean_object* v___x_4591_; size_t v_sz_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v_sz_4590_ = lean_array_size(v___x_4587_);
v___x_4591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__1(v_sz_4590_, v___x_4557_, v___x_4587_);
v_sz_4592_ = lean_array_size(v___y_4589_);
lean_inc_ref(v___y_4589_);
v___x_4593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__2(v___x_4591_, v_sz_4592_, v___x_4557_, v___y_4589_);
v___x_4594_ = lean_expr_instantiate_rev(v_pattern_4539_, v___x_4591_);
lean_dec_ref(v_pattern_4539_);
v___x_4595_ = lean_expr_abstract(v___x_4594_, v___x_4593_);
lean_dec_ref(v___x_4594_);
v___x_4596_ = lean_array_get_size(v___y_4589_);
v___x_4597_ = lean_mk_empty_array_with_capacity(v___x_4596_);
v___x_4598_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3___redArg(v_varTypes_4537_, v___x_4591_, v___x_4593_, v___y_4589_, v___x_4596_, v___x_4552_, v___x_4597_);
lean_dec_ref(v___x_4593_);
lean_dec_ref(v___x_4591_);
lean_dec_ref(v_varTypes_4537_);
if (lean_obj_tag(v_varInfos_x3f_4538_) == 0)
{
v___y_4559_ = v___x_4595_;
v___y_4560_ = v___y_4589_;
v___y_4561_ = v___x_4598_;
v___y_4562_ = v_sz_4592_;
v___y_4563_ = v_varInfos_x3f_4538_;
goto v___jp_4558_;
}
else
{
lean_object* v_val_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4611_; 
v_val_4599_ = lean_ctor_get(v_varInfos_x3f_4538_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v_varInfos_x3f_4538_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4601_ = v_varInfos_x3f_4538_;
v_isShared_4602_ = v_isSharedCheck_4611_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_val_4599_);
lean_dec(v_varInfos_x3f_4538_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4611_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; uint8_t v___x_4605_; 
lean_inc_ref(v___y_4589_);
v___x_4603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__6(v_val_4599_, v_sz_4592_, v___x_4557_, v___y_4589_);
lean_dec(v_val_4599_);
v___x_4604_ = lean_array_get_size(v___x_4603_);
v___x_4605_ = lean_nat_dec_lt(v___x_4552_, v___x_4604_);
if (v___x_4605_ == 0)
{
lean_dec_ref(v___x_4603_);
lean_del_object(v___x_4601_);
v___y_4580_ = v___x_4595_;
v___y_4581_ = v___x_4598_;
v___y_4582_ = v___y_4589_;
v___y_4583_ = v_sz_4592_;
goto v___jp_4579_;
}
else
{
if (v___x_4605_ == 0)
{
lean_dec_ref(v___x_4603_);
lean_del_object(v___x_4601_);
v___y_4580_ = v___x_4595_;
v___y_4581_ = v___x_4598_;
v___y_4582_ = v___y_4589_;
v___y_4583_ = v_sz_4592_;
goto v___jp_4579_;
}
else
{
size_t v___x_4606_; uint8_t v___x_4607_; 
v___x_4606_ = lean_usize_of_nat(v___x_4604_);
v___x_4607_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__7(v___x_4586_, v___x_4603_, v___x_4557_, v___x_4606_);
if (v___x_4607_ == 0)
{
lean_dec_ref(v___x_4603_);
lean_del_object(v___x_4601_);
v___y_4580_ = v___x_4595_;
v___y_4581_ = v___x_4598_;
v___y_4582_ = v___y_4589_;
v___y_4583_ = v_sz_4592_;
goto v___jp_4579_;
}
else
{
lean_object* v___x_4609_; 
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4603_);
v___x_4609_ = v___x_4601_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4603_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
v___y_4559_ = v___x_4595_;
v___y_4560_ = v___y_4589_;
v___y_4561_ = v___x_4598_;
v___y_4562_ = v_sz_4592_;
v___y_4563_ = v___x_4609_;
goto v___jp_4558_;
}
}
}
}
}
}
}
}
v___jp_4558_:
{
if (lean_obj_tag(v_checkTypeMask_x3f_4541_) == 0)
{
lean_object* v___x_4564_; 
lean_dec_ref(v___y_4560_);
v___x_4564_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4564_, 0, v_levelParams_4536_);
lean_ctor_set(v___x_4564_, 1, v___y_4561_);
lean_ctor_set(v___x_4564_, 2, v___y_4563_);
lean_ctor_set(v___x_4564_, 3, v___y_4559_);
lean_ctor_set(v___x_4564_, 4, v_fnInfos_4540_);
lean_ctor_set(v___x_4564_, 5, v_checkTypeMask_x3f_4541_);
return v___x_4564_;
}
else
{
lean_object* v_val_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4578_; 
v_val_4565_ = lean_ctor_get(v_checkTypeMask_x3f_4541_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v_checkTypeMask_x3f_4541_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4567_ = v_checkTypeMask_x3f_4541_;
v_isShared_4568_ = v_isSharedCheck_4578_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_val_4565_);
lean_dec(v_checkTypeMask_x3f_4541_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4578_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; uint8_t v___x_4571_; 
v___x_4569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__4(v_val_4565_, v___y_4562_, v___x_4557_, v___y_4560_);
lean_dec(v_val_4565_);
v___x_4570_ = lean_array_get_size(v___x_4569_);
v___x_4571_ = lean_nat_dec_lt(v___x_4552_, v___x_4570_);
if (v___x_4571_ == 0)
{
lean_dec_ref(v___x_4569_);
lean_del_object(v___x_4567_);
v___y_4543_ = v___y_4563_;
v___y_4544_ = v___y_4559_;
v___y_4545_ = v___y_4561_;
goto v___jp_4542_;
}
else
{
if (v___x_4571_ == 0)
{
lean_dec_ref(v___x_4569_);
lean_del_object(v___x_4567_);
v___y_4543_ = v___y_4563_;
v___y_4544_ = v___y_4559_;
v___y_4545_ = v___y_4561_;
goto v___jp_4542_;
}
else
{
size_t v___x_4572_; uint8_t v___x_4573_; 
v___x_4572_ = lean_usize_of_nat(v___x_4570_);
v___x_4573_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__5(v___x_4569_, v___x_4557_, v___x_4572_);
if (v___x_4573_ == 0)
{
lean_dec_ref(v___x_4569_);
lean_del_object(v___x_4567_);
v___y_4543_ = v___y_4563_;
v___y_4544_ = v___y_4559_;
v___y_4545_ = v___y_4561_;
goto v___jp_4542_;
}
else
{
lean_object* v___x_4575_; 
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 0, v___x_4569_);
v___x_4575_ = v___x_4567_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4569_);
v___x_4575_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
lean_object* v___x_4576_; 
v___x_4576_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4576_, 0, v_levelParams_4536_);
lean_ctor_set(v___x_4576_, 1, v___y_4561_);
lean_ctor_set(v___x_4576_, 2, v___y_4563_);
lean_ctor_set(v___x_4576_, 3, v___y_4559_);
lean_ctor_set(v___x_4576_, 4, v_fnInfos_4540_);
lean_ctor_set(v___x_4576_, 5, v___x_4575_);
return v___x_4576_;
}
}
}
}
}
}
}
v___jp_4579_:
{
lean_object* v___x_4584_; 
v___x_4584_ = lean_box(0);
v___y_4559_ = v___y_4580_;
v___y_4560_ = v___y_4582_;
v___y_4561_ = v___y_4581_;
v___y_4562_ = v___y_4583_;
v___y_4563_ = v___x_4584_;
goto v___jp_4558_;
}
}
}
v___jp_4542_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4546_ = lean_box(0);
v___x_4547_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4547_, 0, v_levelParams_4536_);
lean_ctor_set(v___x_4547_, 1, v___y_4545_);
lean_ctor_set(v___x_4547_, 2, v___y_4543_);
lean_ctor_set(v___x_4547_, 3, v___y_4544_);
lean_ctor_set(v___x_4547_, 4, v_fnInfos_4540_);
lean_ctor_set(v___x_4547_, 5, v___x_4546_);
return v___x_4547_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3(lean_object* v___x_4620_, lean_object* v___x_4621_, lean_object* v___x_4622_, lean_object* v_as_4623_, lean_object* v_i_4624_, lean_object* v_j_4625_, lean_object* v_inv_4626_, lean_object* v_bs_4627_){
_start:
{
lean_object* v___x_4628_; 
v___x_4628_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3___redArg(v___x_4620_, v___x_4621_, v___x_4622_, v_as_4623_, v_i_4624_, v_j_4625_, v_bs_4627_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3___boxed(lean_object* v___x_4629_, lean_object* v___x_4630_, lean_object* v___x_4631_, lean_object* v_as_4632_, lean_object* v_i_4633_, lean_object* v_j_4634_, lean_object* v_inv_4635_, lean_object* v_bs_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__3(v___x_4629_, v___x_4630_, v___x_4631_, v_as_4632_, v_i_4633_, v_j_4634_, v_inv_4635_, v_bs_4636_);
lean_dec_ref(v_as_4632_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4630_);
lean_dec_ref(v___x_4629_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9(lean_object* v_upperBound_4638_, lean_object* v___x_4639_, lean_object* v___x_4640_, uint8_t v___x_4641_, lean_object* v_inst_4642_, lean_object* v_R_4643_, lean_object* v_a_4644_, lean_object* v_b_4645_, lean_object* v_c_4646_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9___redArg(v_upperBound_4638_, v___x_4639_, v___x_4640_, v___x_4641_, v_a_4644_, v_b_4645_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9___boxed(lean_object* v_upperBound_4648_, lean_object* v___x_4649_, lean_object* v___x_4650_, lean_object* v___x_4651_, lean_object* v_inst_4652_, lean_object* v_R_4653_, lean_object* v_a_4654_, lean_object* v_b_4655_, lean_object* v_c_4656_){
_start:
{
uint8_t v___x_5407__boxed_4657_; lean_object* v_res_4658_; 
v___x_5407__boxed_4657_ = lean_unbox(v___x_4651_);
v_res_4658_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__9(v_upperBound_4648_, v___x_4649_, v___x_4650_, v___x_5407__boxed_4657_, v_inst_4652_, v_R_4653_, v_a_4654_, v_b_4655_, v_c_4656_);
lean_dec(v___x_4650_);
lean_dec_ref(v___x_4649_);
lean_dec(v_upperBound_4648_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10(lean_object* v_upperBound_4659_, lean_object* v_n_4660_, lean_object* v___x_4661_, lean_object* v_inst_4662_, lean_object* v_R_4663_, lean_object* v_a_4664_, lean_object* v_b_4665_, lean_object* v_c_4666_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10___redArg(v_upperBound_4659_, v_n_4660_, v___x_4661_, v_a_4664_, v_b_4665_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10___boxed(lean_object* v_upperBound_4668_, lean_object* v_n_4669_, lean_object* v___x_4670_, lean_object* v_inst_4671_, lean_object* v_R_4672_, lean_object* v_a_4673_, lean_object* v_b_4674_, lean_object* v_c_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__10(v_upperBound_4668_, v_n_4669_, v___x_4670_, v_inst_4671_, v_R_4672_, v_a_4673_, v_b_4674_, v_c_4675_);
lean_dec_ref(v___x_4670_);
lean_dec(v_n_4669_);
lean_dec(v_upperBound_4668_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11(lean_object* v_upperBound_4677_, lean_object* v_p_4678_, lean_object* v_n_4679_, lean_object* v_inst_4680_, lean_object* v_R_4681_, lean_object* v_a_4682_, lean_object* v_b_4683_, lean_object* v_c_4684_){
_start:
{
lean_object* v___x_4685_; 
v___x_4685_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11___redArg(v_upperBound_4677_, v_p_4678_, v_n_4679_, v_a_4682_, v_b_4683_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11___boxed(lean_object* v_upperBound_4686_, lean_object* v_p_4687_, lean_object* v_n_4688_, lean_object* v_inst_4689_, lean_object* v_R_4690_, lean_object* v_a_4691_, lean_object* v_b_4692_, lean_object* v_c_4693_){
_start:
{
lean_object* v_res_4694_; 
v_res_4694_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern_spec__11(v_upperBound_4686_, v_p_4687_, v_n_4688_, v_inst_4689_, v_R_4690_, v_a_4691_, v_b_4692_, v_c_4693_);
lean_dec(v_n_4688_);
lean_dec_ref(v_p_4687_);
lean_dec(v_upperBound_4686_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg(lean_object* v_type_4701_, lean_object* v_a_4702_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_4701_, v_a_4702_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4778_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4710_ = v___x_4707_;
v_isShared_4711_ = v_isSharedCheck_4778_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4707_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4778_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4717_; uint8_t v___x_4718_; 
v___x_4717_ = l_Lean_Expr_cleanupAnnotations(v_a_4708_);
v___x_4718_ = l_Lean_Expr_isApp(v___x_4717_);
if (v___x_4718_ == 0)
{
lean_dec_ref(v___x_4717_);
goto v___jp_4712_;
}
else
{
lean_object* v_arg_4719_; lean_object* v___x_4720_; uint8_t v___x_4721_; 
v_arg_4719_ = lean_ctor_get(v___x_4717_, 1);
lean_inc_ref(v_arg_4719_);
v___x_4720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4717_);
v___x_4721_ = l_Lean_Expr_isApp(v___x_4720_);
if (v___x_4721_ == 0)
{
lean_dec_ref(v___x_4720_);
lean_dec_ref(v_arg_4719_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4722_; uint8_t v___x_4723_; 
v___x_4722_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4720_);
v___x_4723_ = l_Lean_Expr_isApp(v___x_4722_);
if (v___x_4723_ == 0)
{
lean_dec_ref(v___x_4722_);
lean_dec_ref(v_arg_4719_);
goto v___jp_4712_;
}
else
{
lean_object* v_arg_4724_; lean_object* v___x_4725_; uint8_t v___x_4726_; 
v_arg_4724_ = lean_ctor_get(v___x_4722_, 1);
lean_inc_ref(v_arg_4724_);
v___x_4725_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4722_);
v___x_4726_ = l_Lean_Expr_isApp(v___x_4725_);
if (v___x_4726_ == 0)
{
lean_dec_ref(v___x_4725_);
lean_dec_ref(v_arg_4724_);
lean_dec_ref(v_arg_4719_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; 
v___x_4727_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4725_);
v___x_4728_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__5));
v___x_4729_ = l_Lean_Expr_isConstOf(v___x_4727_, v___x_4728_);
if (v___x_4729_ == 0)
{
uint8_t v___x_4730_; 
lean_dec_ref(v_arg_4719_);
v___x_4730_ = l_Lean_Expr_isApp(v___x_4727_);
if (v___x_4730_ == 0)
{
lean_dec_ref(v___x_4727_);
lean_dec_ref(v_arg_4724_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4731_; uint8_t v___x_4732_; 
v___x_4731_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4727_);
v___x_4732_ = l_Lean_Expr_isApp(v___x_4731_);
if (v___x_4732_ == 0)
{
lean_dec_ref(v___x_4731_);
lean_dec_ref(v_arg_4724_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4733_; uint8_t v___x_4734_; 
v___x_4733_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4731_);
v___x_4734_ = l_Lean_Expr_isApp(v___x_4733_);
if (v___x_4734_ == 0)
{
lean_dec_ref(v___x_4733_);
lean_dec_ref(v_arg_4724_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4735_; uint8_t v___x_4736_; 
v___x_4735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4733_);
v___x_4736_ = l_Lean_Expr_isApp(v___x_4735_);
if (v___x_4736_ == 0)
{
lean_dec_ref(v___x_4735_);
lean_dec_ref(v_arg_4724_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4737_; uint8_t v___x_4738_; 
v___x_4737_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4735_);
v___x_4738_ = l_Lean_Expr_isApp(v___x_4737_);
if (v___x_4738_ == 0)
{
lean_dec_ref(v___x_4737_);
lean_dec_ref(v_arg_4724_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4739_; uint8_t v___x_4740_; 
v___x_4739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4737_);
v___x_4740_ = l_Lean_Expr_isApp(v___x_4739_);
if (v___x_4740_ == 0)
{
lean_dec_ref(v___x_4739_);
lean_dec_ref(v_arg_4724_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4741_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4739_);
v___x_4742_ = l_Lean_Expr_isApp(v___x_4741_);
if (v___x_4742_ == 0)
{
lean_dec_ref(v___x_4741_);
lean_dec_ref(v_arg_4724_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4743_; uint8_t v___x_4744_; 
v___x_4743_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4741_);
v___x_4744_ = l_Lean_Expr_isApp(v___x_4743_);
if (v___x_4744_ == 0)
{
lean_dec_ref(v___x_4743_);
lean_dec_ref(v_arg_4724_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; 
v___x_4745_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4743_);
v___x_4746_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_tripleToWpProof_x3f___closed__1));
v___x_4747_ = l_Lean_Expr_isConstOf(v___x_4745_, v___x_4746_);
lean_dec_ref(v___x_4745_);
if (v___x_4747_ == 0)
{
lean_dec_ref(v_arg_4724_);
goto v___jp_4712_;
}
else
{
lean_object* v___x_4748_; lean_object* v___x_4749_; 
lean_del_object(v___x_4710_);
v___x_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4748_, 0, v_arg_4724_);
v___x_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4748_);
return v___x_4749_;
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
else
{
lean_object* v___x_4750_; uint8_t v___x_4751_; 
lean_dec_ref(v___x_4727_);
lean_dec_ref(v_arg_4724_);
lean_del_object(v___x_4710_);
v___x_4750_ = l_Lean_Expr_cleanupAnnotations(v_arg_4719_);
v___x_4751_ = l_Lean_Expr_isApp(v___x_4750_);
if (v___x_4751_ == 0)
{
lean_dec_ref(v___x_4750_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4752_; uint8_t v___x_4753_; 
v___x_4752_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4750_);
v___x_4753_ = l_Lean_Expr_isApp(v___x_4752_);
if (v___x_4753_ == 0)
{
lean_dec_ref(v___x_4752_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4754_; uint8_t v___x_4755_; 
v___x_4754_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4752_);
v___x_4755_ = l_Lean_Expr_isApp(v___x_4754_);
if (v___x_4755_ == 0)
{
lean_dec_ref(v___x_4754_);
goto v___jp_4704_;
}
else
{
lean_object* v_arg_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; 
v_arg_4756_ = lean_ctor_get(v___x_4754_, 1);
lean_inc_ref(v_arg_4756_);
v___x_4757_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4754_);
v___x_4758_ = l_Lean_Expr_isApp(v___x_4757_);
if (v___x_4758_ == 0)
{
lean_dec_ref(v___x_4757_);
lean_dec_ref(v_arg_4756_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4759_; uint8_t v___x_4760_; 
v___x_4759_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4757_);
v___x_4760_ = l_Lean_Expr_isApp(v___x_4759_);
if (v___x_4760_ == 0)
{
lean_dec_ref(v___x_4759_);
lean_dec_ref(v_arg_4756_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4761_; uint8_t v___x_4762_; 
v___x_4761_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4759_);
v___x_4762_ = l_Lean_Expr_isApp(v___x_4761_);
if (v___x_4762_ == 0)
{
lean_dec_ref(v___x_4761_);
lean_dec_ref(v_arg_4756_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4763_; uint8_t v___x_4764_; 
v___x_4763_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4761_);
v___x_4764_ = l_Lean_Expr_isApp(v___x_4763_);
if (v___x_4764_ == 0)
{
lean_dec_ref(v___x_4763_);
lean_dec_ref(v_arg_4756_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4765_; uint8_t v___x_4766_; 
v___x_4765_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4763_);
v___x_4766_ = l_Lean_Expr_isApp(v___x_4765_);
if (v___x_4766_ == 0)
{
lean_dec_ref(v___x_4765_);
lean_dec_ref(v_arg_4756_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4767_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4765_);
v___x_4768_ = l_Lean_Expr_isApp(v___x_4767_);
if (v___x_4768_ == 0)
{
lean_dec_ref(v___x_4767_);
lean_dec_ref(v_arg_4756_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4769_; uint8_t v___x_4770_; 
v___x_4769_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4767_);
v___x_4770_ = l_Lean_Expr_isApp(v___x_4769_);
if (v___x_4770_ == 0)
{
lean_dec_ref(v___x_4769_);
lean_dec_ref(v_arg_4756_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4771_; uint8_t v___x_4772_; 
v___x_4771_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4769_);
v___x_4772_ = l_Lean_Expr_isApp(v___x_4771_);
if (v___x_4772_ == 0)
{
lean_dec_ref(v___x_4771_);
lean_dec_ref(v_arg_4756_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4773_; lean_object* v___x_4774_; uint8_t v___x_4775_; 
v___x_4773_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4771_);
v___x_4774_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___closed__1));
v___x_4775_ = l_Lean_Expr_isConstOf(v___x_4773_, v___x_4774_);
lean_dec_ref(v___x_4773_);
if (v___x_4775_ == 0)
{
lean_dec_ref(v_arg_4756_);
goto v___jp_4704_;
}
else
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4776_, 0, v_arg_4756_);
v___x_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
return v___x_4777_;
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
}
}
}
}
}
}
v___jp_4712_:
{
lean_object* v___x_4713_; lean_object* v___x_4715_; 
v___x_4713_ = lean_box(0);
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 0, v___x_4713_);
v___x_4715_ = v___x_4710_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4713_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
else
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4786_; 
v_a_4779_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4781_ = v___x_4707_;
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4707_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4784_; 
if (v_isShared_4782_ == 0)
{
v___x_4784_ = v___x_4781_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4779_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
v___jp_4704_:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4705_ = lean_box(0);
v___x_4706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4705_);
return v___x_4706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg___boxed(lean_object* v_type_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg(v_type_4787_, v_a_4788_);
lean_dec(v_a_4788_);
return v_res_4790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg(lean_object* v_type_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_){
_start:
{
lean_object* v___x_4797_; 
v___x_4797_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg(v_type_4791_, v_a_4793_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___boxed(lean_object* v_type_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_){
_start:
{
lean_object* v_res_4804_; 
v_res_4804_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg(v_type_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
return v_res_4804_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4806_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___closed__0));
v___x_4807_ = l_Lean_stringToMessageData(v___x_4806_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0(lean_object* v_type_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
lean_object* v___x_4814_; 
lean_inc_ref(v_type_4808_);
v___x_4814_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg(v_type_4808_, v___y_4810_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4829_; 
v_a_4815_ = lean_ctor_get(v___x_4814_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4814_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4817_ = v___x_4814_;
v_isShared_4818_ = v_isSharedCheck_4829_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___x_4814_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4829_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
if (lean_obj_tag(v_a_4815_) == 1)
{
lean_object* v_val_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4823_; 
lean_dec_ref(v_type_4808_);
v_val_4819_ = lean_ctor_get(v_a_4815_, 0);
lean_inc(v_val_4819_);
lean_dec_ref_known(v_a_4815_, 1);
v___x_4820_ = lean_box(0);
v___x_4821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4821_, 0, v_val_4819_);
lean_ctor_set(v___x_4821_, 1, v___x_4820_);
if (v_isShared_4818_ == 0)
{
lean_ctor_set(v___x_4817_, 0, v___x_4821_);
v___x_4823_ = v___x_4817_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4821_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
else
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
lean_del_object(v___x_4817_);
lean_dec(v_a_4815_);
v___x_4825_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___closed__1);
v___x_4826_ = l_Lean_indentExpr(v_type_4808_);
v___x_4827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4825_);
lean_ctor_set(v___x_4827_, 1, v___x_4826_);
v___x_4828_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_4827_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
return v___x_4828_;
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
lean_dec_ref(v_type_4808_);
v_a_4830_ = lean_ctor_get(v___x_4814_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4814_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4814_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4814_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4835_; 
if (v_isShared_4833_ == 0)
{
v___x_4835_ = v___x_4832_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0___boxed(lean_object* v_type_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___lam__0(v_type_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
lean_dec(v___y_4842_);
lean_dec_ref(v___y_4841_);
lean_dec(v___y_4840_);
lean_dec_ref(v___y_4839_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr(lean_object* v_expr_4848_, lean_object* v_levelParams_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_){
_start:
{
lean_object* v___x_4855_; 
v___x_4855_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessExprPattern(v_expr_4848_, v_levelParams_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v_a_4856_; lean_object* v_fst_4857_; lean_object* v_snd_4858_; lean_object* v___f_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc(v_a_4856_);
lean_dec_ref_known(v___x_4855_, 1);
v_fst_4857_ = lean_ctor_get(v_a_4856_, 0);
lean_inc(v_fst_4857_);
v_snd_4858_ = lean_ctor_get(v_a_4856_, 1);
lean_inc_n(v_snd_4858_, 2);
lean_dec(v_a_4856_);
v___f_4859_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___closed__0));
v___x_4860_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___closed__1));
v___x_4861_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(lean_box(0), v_fst_4857_, v_snd_4858_, v___f_4859_, v_snd_4858_, v___x_4860_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4871_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4864_ = v___x_4861_;
v_isShared_4865_ = v_isSharedCheck_4871_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4861_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4871_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v_fst_4866_; lean_object* v___x_4867_; lean_object* v___x_4869_; 
v_fst_4866_ = lean_ctor_get(v_a_4862_, 0);
lean_inc(v_fst_4866_);
lean_dec(v_a_4862_);
v___x_4867_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_eraseUnusedVarsFromPattern(v_fst_4866_);
if (v_isShared_4865_ == 0)
{
lean_ctor_set(v___x_4864_, 0, v___x_4867_);
v___x_4869_ = v___x_4864_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v___x_4867_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
v_a_4872_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4861_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4861_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
v_a_4880_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4855_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4855_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr___boxed(lean_object* v_expr_4888_, lean_object* v_levelParams_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr(v_expr_4888_, v_levelParams_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
lean_dec(v_a_4893_);
lean_dec_ref(v_a_4892_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheorem(lean_object* v_type_4896_, lean_object* v_proof_4897_, lean_object* v_prio_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_){
_start:
{
lean_object* v___x_4904_; 
lean_inc_ref(v_proof_4897_);
v___x_4904_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_getProof(v_proof_4897_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v_a_4905_; lean_object* v_fst_4906_; lean_object* v_snd_4907_; lean_object* v___x_4908_; lean_object* v_a_4909_; uint8_t v___x_4910_; lean_object* v___x_4911_; 
v_a_4905_ = lean_ctor_get(v___x_4904_, 0);
lean_inc(v_a_4905_);
lean_dec_ref_known(v___x_4904_, 1);
v_fst_4906_ = lean_ctor_get(v_a_4905_, 0);
lean_inc(v_fst_4906_);
v_snd_4907_ = lean_ctor_get(v_a_4905_, 1);
lean_inc(v_snd_4907_);
lean_dec(v_a_4905_);
v___x_4908_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_type_4896_, v_a_4900_);
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4909_);
lean_dec_ref(v___x_4908_);
v___x_4910_ = 0;
v___x_4911_ = l_Lean_Meta_forallMetaTelescope(v_a_4909_, v___x_4910_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; lean_object* v_snd_4913_; lean_object* v_snd_4914_; lean_object* v___x_4915_; 
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
lean_inc(v_a_4912_);
lean_dec_ref_known(v___x_4911_, 1);
v_snd_4913_ = lean_ctor_get(v_a_4912_, 1);
lean_inc(v_snd_4913_);
lean_dec(v_a_4912_);
v_snd_4914_ = lean_ctor_get(v_snd_4913_, 1);
lean_inc(v_snd_4914_);
lean_dec(v_snd_4913_);
v___x_4915_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_selectProg___redArg(v_snd_4914_, v_a_4900_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4951_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4918_ = v___x_4915_;
v_isShared_4919_ = v_isSharedCheck_4951_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4915_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4951_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
if (lean_obj_tag(v_a_4916_) == 1)
{
lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4945_; 
lean_del_object(v___x_4918_);
v_isSharedCheck_4945_ = !lean_is_exclusive(v_a_4916_);
if (v_isSharedCheck_4945_ == 0)
{
lean_object* v_unused_4946_; 
v_unused_4946_ = lean_ctor_get(v_a_4916_, 0);
lean_dec(v_unused_4946_);
v___x_4921_ = v_a_4916_;
v_isShared_4922_ = v_isSharedCheck_4945_;
goto v_resetjp_4920_;
}
else
{
lean_dec(v_a_4916_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4945_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4923_; 
v___x_4923_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecPatternFromExpr(v_snd_4907_, v_fst_4906_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4936_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4926_ = v___x_4923_;
v_isShared_4927_ = v_isSharedCheck_4936_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4923_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4936_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4931_; 
v___x_4928_ = lean_box(0);
v___x_4929_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4929_, 0, v_a_4924_);
lean_ctor_set(v___x_4929_, 1, v_proof_4897_);
lean_ctor_set(v___x_4929_, 2, v___x_4928_);
lean_ctor_set(v___x_4929_, 3, v_prio_4898_);
if (v_isShared_4922_ == 0)
{
lean_ctor_set(v___x_4921_, 0, v___x_4929_);
v___x_4931_ = v___x_4921_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4929_);
v___x_4931_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4933_; 
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 0, v___x_4931_);
v___x_4933_ = v___x_4926_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
else
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4944_; 
lean_del_object(v___x_4921_);
lean_dec(v_prio_4898_);
lean_dec_ref(v_proof_4897_);
v_a_4937_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4939_ = v___x_4923_;
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4923_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4942_; 
if (v_isShared_4940_ == 0)
{
v___x_4942_ = v___x_4939_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_a_4937_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
}
}
else
{
lean_object* v___x_4947_; lean_object* v___x_4949_; 
lean_dec(v_a_4916_);
lean_dec(v_snd_4907_);
lean_dec(v_fst_4906_);
lean_dec(v_prio_4898_);
lean_dec_ref(v_proof_4897_);
v___x_4947_ = lean_box(0);
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 0, v___x_4947_);
v___x_4949_ = v___x_4918_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec(v_snd_4907_);
lean_dec(v_fst_4906_);
lean_dec(v_prio_4898_);
lean_dec_ref(v_proof_4897_);
v_a_4952_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4915_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4915_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
else
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4967_; 
lean_dec(v_snd_4907_);
lean_dec(v_fst_4906_);
lean_dec(v_prio_4898_);
lean_dec_ref(v_proof_4897_);
v_a_4960_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4962_ = v___x_4911_;
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4911_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4965_; 
if (v_isShared_4963_ == 0)
{
v___x_4965_ = v___x_4962_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_a_4960_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
else
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
lean_dec(v_prio_4898_);
lean_dec_ref(v_proof_4897_);
lean_dec_ref(v_type_4896_);
v_a_4968_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4904_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4904_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheorem___boxed(lean_object* v_type_4976_, lean_object* v_proof_4977_, lean_object* v_prio_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheorem(v_type_4976_, v_proof_4977_, v_prio_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_);
lean_dec(v_a_4982_);
lean_dec_ref(v_a_4981_);
lean_dec(v_a_4980_);
lean_dec_ref(v_a_4979_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromConst(lean_object* v_declName_4985_, lean_object* v_prio_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_){
_start:
{
lean_object* v___x_4992_; 
lean_inc(v_declName_4985_);
v___x_4992_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_4985_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v_a_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
lean_inc(v_a_4993_);
lean_dec_ref_known(v___x_4992_, 1);
v___x_4994_ = l_Lean_ConstantInfo_type(v_a_4993_);
lean_dec(v_a_4993_);
v___x_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4995_, 0, v_declName_4985_);
v___x_4996_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheorem(v___x_4994_, v___x_4995_, v_prio_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_);
return v___x_4996_;
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
lean_dec(v_prio_4986_);
lean_dec(v_declName_4985_);
v_a_4997_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v___x_4992_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4992_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5002_; 
if (v_isShared_5000_ == 0)
{
v___x_5002_ = v___x_4999_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromConst___boxed(lean_object* v_declName_5005_, lean_object* v_prio_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromConst(v_declName_5005_, v_prio_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(lean_object* v_fvar_5013_, lean_object* v_prio_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_){
_start:
{
lean_object* v___x_5020_; 
lean_inc(v_fvar_5013_);
v___x_5020_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvar_5013_, v_a_5015_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5021_; 
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc(v_a_5021_);
lean_dec_ref_known(v___x_5020_, 1);
if (lean_obj_tag(v_a_5021_) == 1)
{
lean_object* v_val_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5031_; 
v_val_5022_ = lean_ctor_get(v_a_5021_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v_a_5021_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5024_ = v_a_5021_;
v_isShared_5025_ = v_isSharedCheck_5031_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_val_5022_);
lean_dec(v_a_5021_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5031_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5026_; lean_object* v___x_5028_; 
v___x_5026_ = l_Lean_LocalDecl_type(v_val_5022_);
lean_dec(v_val_5022_);
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 0, v_fvar_5013_);
v___x_5028_ = v___x_5024_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_fvar_5013_);
v___x_5028_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
lean_object* v___x_5029_; 
v___x_5029_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheorem(v___x_5026_, v___x_5028_, v_prio_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5029_;
}
}
}
else
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
lean_dec(v_a_5021_);
lean_dec(v_prio_5014_);
v___x_5032_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1);
v___x_5033_ = l_Lean_MessageData_ofName(v_fvar_5013_);
v___x_5034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5032_);
lean_ctor_set(v___x_5034_, 1, v___x_5033_);
v___x_5035_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3);
v___x_5036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5034_);
lean_ctor_set(v___x_5036_, 1, v___x_5035_);
v___x_5037_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_5036_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5037_;
}
}
else
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5045_; 
lean_dec(v_prio_5014_);
lean_dec(v_fvar_5013_);
v_a_5038_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5040_ = v___x_5020_;
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_5020_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5043_; 
if (v_isShared_5041_ == 0)
{
v___x_5043_ = v___x_5040_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_a_5038_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal___boxed(lean_object* v_fvar_5046_, lean_object* v_prio_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(v_fvar_5046_, v_prio_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_);
lean_dec(v_a_5051_);
lean_dec_ref(v_a_5050_);
lean_dec(v_a_5049_);
lean_dec_ref(v_a_5048_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromStx(lean_object* v_ref_5054_, lean_object* v_proof_5055_, lean_object* v_prio_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_){
_start:
{
lean_object* v___x_5062_; 
lean_inc(v_a_5060_);
lean_inc_ref(v_a_5059_);
lean_inc(v_a_5058_);
lean_inc_ref(v_a_5057_);
lean_inc_ref(v_proof_5055_);
v___x_5062_ = lean_infer_type(v_proof_5055_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5064_; lean_object* v_a_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
lean_dec_ref_known(v___x_5062_, 1);
v___x_5064_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v_a_5060_);
v_a_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_a_5065_);
lean_dec_ref(v___x_5064_);
v___x_5066_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_5066_, 0, v_a_5065_);
lean_ctor_set(v___x_5066_, 1, v_ref_5054_);
lean_ctor_set(v___x_5066_, 2, v_proof_5055_);
v___x_5067_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheorem(v_a_5063_, v___x_5066_, v_prio_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_);
return v___x_5067_;
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_dec(v_prio_5056_);
lean_dec_ref(v_proof_5055_);
lean_dec(v_ref_5054_);
v_a_5068_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5062_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5062_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromStx___boxed(lean_object* v_ref_5076_, lean_object* v_proof_5077_, lean_object* v_prio_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromStx(v_ref_5076_, v_proof_5077_, v_prio_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
lean_dec(v_a_5082_);
lean_dec_ref(v_a_5081_);
lean_dec(v_a_5080_);
lean_dec_ref(v_a_5079_);
return v_res_5084_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__1(void){
_start:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5086_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__0));
v___x_5087_ = l_Lean_stringToMessageData(v___x_5086_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst(lean_object* v_ext_5088_, lean_object* v_declName_5089_, lean_object* v_prio_5090_, uint8_t v_attrKind_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_){
_start:
{
lean_object* v___x_5097_; 
v___x_5097_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromConst(v_declName_5089_, v_prio_5090_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v_a_5098_; 
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v___x_5097_, 1);
if (lean_obj_tag(v_a_5098_) == 1)
{
lean_object* v_val_5099_; lean_object* v___x_5100_; 
v_val_5099_ = lean_ctor_get(v_a_5098_, 0);
lean_inc(v_val_5099_);
lean_dec_ref_known(v_a_5098_, 1);
v___x_5100_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_5088_, v_val_5099_, v_attrKind_5091_, v_a_5093_, v_a_5094_, v_a_5095_);
return v___x_5100_;
}
else
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
lean_dec(v_a_5098_);
lean_dec_ref(v_ext_5088_);
v___x_5101_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__1, &l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__1);
v___x_5102_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_5101_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_);
return v___x_5102_;
}
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_dec_ref(v_ext_5088_);
v_a_5103_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_5097_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_5097_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___boxed(lean_object* v_ext_5111_, lean_object* v_declName_5112_, lean_object* v_prio_5113_, lean_object* v_attrKind_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_){
_start:
{
uint8_t v_attrKind_boxed_5120_; lean_object* v_res_5121_; 
v_attrKind_boxed_5120_ = lean_unbox(v_attrKind_5114_);
v_res_5121_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst(v_ext_5111_, v_declName_5112_, v_prio_5113_, v_attrKind_boxed_5120_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_);
lean_dec(v_a_5118_);
lean_dec_ref(v_a_5117_);
lean_dec(v_a_5116_);
lean_dec_ref(v_a_5115_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromLocal(lean_object* v_ext_5122_, lean_object* v_fvar_5123_, lean_object* v_prio_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_){
_start:
{
lean_object* v___x_5130_; 
v___x_5130_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(v_fvar_5123_, v_prio_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
lean_dec_ref_known(v___x_5130_, 1);
if (lean_obj_tag(v_a_5131_) == 1)
{
lean_object* v_val_5132_; uint8_t v___x_5133_; lean_object* v___x_5134_; 
v_val_5132_ = lean_ctor_get(v_a_5131_, 0);
lean_inc(v_val_5132_);
lean_dec_ref_known(v_a_5131_, 1);
v___x_5133_ = 1;
v___x_5134_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_5122_, v_val_5132_, v___x_5133_, v_a_5126_, v_a_5127_, v_a_5128_);
return v___x_5134_;
}
else
{
lean_object* v___x_5135_; lean_object* v___x_5136_; 
lean_dec(v_a_5131_);
lean_dec_ref(v_ext_5122_);
v___x_5135_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__1, &l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst___closed__1);
v___x_5136_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_5135_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
return v___x_5136_;
}
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
lean_dec_ref(v_ext_5122_);
v_a_5137_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5130_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5130_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromLocal___boxed(lean_object* v_ext_5145_, lean_object* v_fvar_5146_, lean_object* v_prio_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromLocal(v_ext_5145_, v_fvar_5146_, v_prio_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_);
lean_dec(v_a_5151_);
lean_dec_ref(v_a_5150_);
lean_dec(v_a_5149_);
lean_dec_ref(v_a_5148_);
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__0(lean_object* v_x_5154_, lean_object* v_a_5155_){
_start:
{
lean_object* v___x_5156_; lean_object* v___x_5157_; 
v___x_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5156_, 0, v_a_5155_);
lean_inc_ref_n(v___x_5156_, 2);
v___x_5157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5157_, 0, v___x_5156_);
lean_ctor_set(v___x_5157_, 1, v___x_5156_);
lean_ctor_set(v___x_5157_, 2, v___x_5156_);
return v___x_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__0___boxed(lean_object* v_x_5158_, lean_object* v_a_5159_){
_start:
{
lean_object* v_res_5160_; 
v_res_5160_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__0(v_x_5158_, v_a_5159_);
lean_dec_ref(v_x_5158_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__1(lean_object* v___y_5161_){
_start:
{
lean_inc_ref(v___y_5161_);
return v___y_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__1___boxed(lean_object* v___y_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___lam__1(v___y_5162_);
lean_dec_ref(v___y_5162_);
return v_res_5163_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__5(void){
_start:
{
lean_object* v___f_5170_; lean_object* v___f_5171_; lean_object* v___x_5172_; lean_object* v___f_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; 
v___f_5170_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__1));
v___f_5171_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__2));
v___x_5172_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__2, &l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default___closed__2);
v___f_5173_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__0));
v___x_5174_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__4));
v___x_5175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5175_, 0, v___x_5174_);
lean_ctor_set(v___x_5175_, 1, v___f_5173_);
lean_ctor_set(v___x_5175_, 2, v___x_5172_);
lean_ctor_set(v___x_5175_, 3, v___f_5171_);
lean_ctor_set(v___x_5175_, 4, v___f_5170_);
return v___x_5175_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt(void){
_start:
{
lean_object* v___x_5176_; 
v___x_5176_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__5, &l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt___closed__5);
return v___x_5176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486626____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5178_; lean_object* v___x_5179_; 
v___x_5178_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt;
v___x_5179_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_5178_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486626____hygCtx___hyg_2____boxed(lean_object* v_a_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486626____hygCtx___hyg_2_();
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems___redArg(lean_object* v_ext_5182_, lean_object* v_a_5183_){
_start:
{
lean_object* v___x_5185_; lean_object* v_ext_5186_; lean_object* v_toEnvExtension_5187_; lean_object* v_env_5188_; lean_object* v_asyncMode_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5185_ = lean_st_ref_get(v_a_5183_);
v_ext_5186_ = lean_ctor_get(v_ext_5182_, 1);
v_toEnvExtension_5187_ = lean_ctor_get(v_ext_5186_, 0);
v_env_5188_ = lean_ctor_get(v___x_5185_, 0);
lean_inc_ref(v_env_5188_);
lean_dec(v___x_5185_);
v_asyncMode_5189_ = lean_ctor_get(v_toEnvExtension_5187_, 2);
v___x_5190_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default;
v___x_5191_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5190_, v_ext_5182_, v_env_5188_, v_asyncMode_5189_);
v___x_5192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5191_);
return v___x_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems___redArg___boxed(lean_object* v_ext_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_){
_start:
{
lean_object* v_res_5196_; 
v_res_5196_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_5193_, v_a_5194_);
lean_dec(v_a_5194_);
lean_dec_ref(v_ext_5193_);
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems(lean_object* v_ext_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_){
_start:
{
lean_object* v___x_5201_; 
v___x_5201_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_5197_, v_a_5199_);
return v___x_5201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems___boxed(lean_object* v_ext_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems(v_ext_5202_, v_a_5203_, v_a_5204_);
lean_dec(v_a_5204_);
lean_dec_ref(v_a_5203_);
lean_dec_ref(v_ext_5202_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems___redArg(lean_object* v_a_5207_){
_start:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; 
v___x_5209_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_specAttr;
v___x_5210_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_getTheorems___redArg(v___x_5209_, v_a_5207_);
return v___x_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems___redArg___boxed(lean_object* v_a_5211_, lean_object* v_a_5212_){
_start:
{
lean_object* v_res_5213_; 
v_res_5213_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems___redArg(v_a_5211_);
lean_dec(v_a_5211_);
return v_res_5213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems(lean_object* v_a_5214_, lean_object* v_a_5215_){
_start:
{
lean_object* v___x_5217_; 
v___x_5217_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems___redArg(v_a_5215_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems___boxed(lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems(v_a_5218_, v_a_5219_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
return v_res_5221_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5223_; lean_object* v___x_5224_; 
v___x_5223_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0));
v___x_5224_ = l_Lean_stringToMessageData(v___x_5223_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(lean_object* v_____r_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; 
v___x_5231_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1);
v___x_5232_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_5231_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed(lean_object* v_____r_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_){
_start:
{
lean_object* v_res_5239_; 
v_res_5239_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(v_____r_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_);
lean_dec(v___y_5237_);
lean_dec_ref(v___y_5236_);
lean_dec(v___y_5235_);
lean_dec_ref(v___y_5234_);
return v_res_5239_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0(void){
_start:
{
lean_object* v___x_5240_; double v___x_5241_; 
v___x_5240_ = lean_unsigned_to_nat(0u);
v___x_5241_ = lean_float_of_nat(v___x_5240_);
return v___x_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(lean_object* v_cls_5245_, lean_object* v_msg_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v_ref_5252_; lean_object* v___x_5253_; lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5298_; 
v_ref_5252_ = lean_ctor_get(v___y_5249_, 5);
v___x_5253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5256_ = v___x_5253_;
v_isShared_5257_ = v_isSharedCheck_5298_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5253_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5298_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5258_; lean_object* v_traceState_5259_; lean_object* v_env_5260_; lean_object* v_nextMacroScope_5261_; lean_object* v_ngen_5262_; lean_object* v_auxDeclNGen_5263_; lean_object* v_cache_5264_; lean_object* v_messages_5265_; lean_object* v_infoState_5266_; lean_object* v_snapshotTasks_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5297_; 
v___x_5258_ = lean_st_ref_take(v___y_5250_);
v_traceState_5259_ = lean_ctor_get(v___x_5258_, 4);
v_env_5260_ = lean_ctor_get(v___x_5258_, 0);
v_nextMacroScope_5261_ = lean_ctor_get(v___x_5258_, 1);
v_ngen_5262_ = lean_ctor_get(v___x_5258_, 2);
v_auxDeclNGen_5263_ = lean_ctor_get(v___x_5258_, 3);
v_cache_5264_ = lean_ctor_get(v___x_5258_, 5);
v_messages_5265_ = lean_ctor_get(v___x_5258_, 6);
v_infoState_5266_ = lean_ctor_get(v___x_5258_, 7);
v_snapshotTasks_5267_ = lean_ctor_get(v___x_5258_, 8);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5258_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5269_ = v___x_5258_;
v_isShared_5270_ = v_isSharedCheck_5297_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_snapshotTasks_5267_);
lean_inc(v_infoState_5266_);
lean_inc(v_messages_5265_);
lean_inc(v_cache_5264_);
lean_inc(v_traceState_5259_);
lean_inc(v_auxDeclNGen_5263_);
lean_inc(v_ngen_5262_);
lean_inc(v_nextMacroScope_5261_);
lean_inc(v_env_5260_);
lean_dec(v___x_5258_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5297_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
uint64_t v_tid_5271_; lean_object* v_traces_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5296_; 
v_tid_5271_ = lean_ctor_get_uint64(v_traceState_5259_, sizeof(void*)*1);
v_traces_5272_ = lean_ctor_get(v_traceState_5259_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v_traceState_5259_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5274_ = v_traceState_5259_;
v_isShared_5275_ = v_isSharedCheck_5296_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_traces_5272_);
lean_dec(v_traceState_5259_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5296_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___x_5276_; double v___x_5277_; uint8_t v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5286_; 
v___x_5276_ = lean_box(0);
v___x_5277_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0);
v___x_5278_ = 0;
v___x_5279_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1));
v___x_5280_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5280_, 0, v_cls_5245_);
lean_ctor_set(v___x_5280_, 1, v___x_5276_);
lean_ctor_set(v___x_5280_, 2, v___x_5279_);
lean_ctor_set_float(v___x_5280_, sizeof(void*)*3, v___x_5277_);
lean_ctor_set_float(v___x_5280_, sizeof(void*)*3 + 8, v___x_5277_);
lean_ctor_set_uint8(v___x_5280_, sizeof(void*)*3 + 16, v___x_5278_);
v___x_5281_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2));
v___x_5282_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5282_, 0, v___x_5280_);
lean_ctor_set(v___x_5282_, 1, v_a_5254_);
lean_ctor_set(v___x_5282_, 2, v___x_5281_);
lean_inc(v_ref_5252_);
v___x_5283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5283_, 0, v_ref_5252_);
lean_ctor_set(v___x_5283_, 1, v___x_5282_);
v___x_5284_ = l_Lean_PersistentArray_push___redArg(v_traces_5272_, v___x_5283_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 0, v___x_5284_);
v___x_5286_ = v___x_5274_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v___x_5284_);
lean_ctor_set_uint64(v_reuseFailAlloc_5295_, sizeof(void*)*1, v_tid_5271_);
v___x_5286_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
lean_object* v___x_5288_; 
if (v_isShared_5270_ == 0)
{
lean_ctor_set(v___x_5269_, 4, v___x_5286_);
v___x_5288_ = v___x_5269_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_env_5260_);
lean_ctor_set(v_reuseFailAlloc_5294_, 1, v_nextMacroScope_5261_);
lean_ctor_set(v_reuseFailAlloc_5294_, 2, v_ngen_5262_);
lean_ctor_set(v_reuseFailAlloc_5294_, 3, v_auxDeclNGen_5263_);
lean_ctor_set(v_reuseFailAlloc_5294_, 4, v___x_5286_);
lean_ctor_set(v_reuseFailAlloc_5294_, 5, v_cache_5264_);
lean_ctor_set(v_reuseFailAlloc_5294_, 6, v_messages_5265_);
lean_ctor_set(v_reuseFailAlloc_5294_, 7, v_infoState_5266_);
lean_ctor_set(v_reuseFailAlloc_5294_, 8, v_snapshotTasks_5267_);
v___x_5288_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5292_; 
v___x_5289_ = lean_st_ref_set(v___y_5250_, v___x_5288_);
v___x_5290_ = lean_box(0);
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 0, v___x_5290_);
v___x_5292_ = v___x_5256_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v___x_5290_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___boxed(lean_object* v_cls_5299_, lean_object* v_msg_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v_cls_5299_, v_msg_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(lean_object* v_constName_5307_, uint8_t v_skipRealize_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v___x_5314_; lean_object* v_env_5315_; lean_object* v___x_5316_; 
v___x_5314_ = lean_st_ref_get(v___y_5312_);
v_env_5315_ = lean_ctor_get(v___x_5314_, 0);
lean_inc_ref(v_env_5315_);
lean_dec(v___x_5314_);
lean_inc(v_constName_5307_);
v___x_5316_ = l_Lean_Environment_findAsync_x3f(v_env_5315_, v_constName_5307_, v_skipRealize_5308_);
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_object* v___x_5317_; 
v___x_5317_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_5307_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
return v___x_5317_;
}
else
{
lean_object* v_val_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5325_; 
lean_dec(v_constName_5307_);
v_val_5318_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5320_ = v___x_5316_;
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_val_5318_);
lean_dec(v___x_5316_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
lean_ctor_set_tag(v___x_5320_, 0);
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_val_5318_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0___boxed(lean_object* v_constName_5326_, lean_object* v_skipRealize_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
uint8_t v_skipRealize_boxed_5333_; lean_object* v_res_5334_; 
v_skipRealize_boxed_5333_ = lean_unbox(v_skipRealize_5327_);
v_res_5334_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_constName_5326_, v_skipRealize_boxed_5333_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
return v_res_5334_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5341_; uint64_t v___x_5342_; 
v___x_5341_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0));
v___x_5342_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5341_);
return v___x_5342_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; 
v___x_5343_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1);
v___x_5344_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0));
v___x_5345_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5345_, 0, v___x_5344_);
lean_ctor_set_uint64(v___x_5345_, sizeof(void*)*1, v___x_5343_);
return v___x_5345_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5346_; 
v___x_5346_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5346_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5347_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3);
v___x_5348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5348_, 0, v___x_5347_);
return v___x_5348_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; 
v___x_5349_ = lean_box(1);
v___x_5350_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_5351_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_5352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5352_, 0, v___x_5351_);
lean_ctor_set(v___x_5352_, 1, v___x_5350_);
lean_ctor_set(v___x_5352_, 2, v___x_5349_);
return v___x_5352_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; 
v___x_5355_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_5356_ = lean_unsigned_to_nat(0u);
v___x_5357_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5357_, 0, v___x_5356_);
lean_ctor_set(v___x_5357_, 1, v___x_5356_);
lean_ctor_set(v___x_5357_, 2, v___x_5356_);
lean_ctor_set(v___x_5357_, 3, v___x_5356_);
lean_ctor_set(v___x_5357_, 4, v___x_5355_);
lean_ctor_set(v___x_5357_, 5, v___x_5355_);
lean_ctor_set(v___x_5357_, 6, v___x_5355_);
lean_ctor_set(v___x_5357_, 7, v___x_5355_);
lean_ctor_set(v___x_5357_, 8, v___x_5355_);
lean_ctor_set(v___x_5357_, 9, v___x_5355_);
return v___x_5357_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5358_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_5359_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5359_, 0, v___x_5358_);
lean_ctor_set(v___x_5359_, 1, v___x_5358_);
lean_ctor_set(v___x_5359_, 2, v___x_5358_);
lean_ctor_set(v___x_5359_, 3, v___x_5358_);
lean_ctor_set(v___x_5359_, 4, v___x_5358_);
lean_ctor_set(v___x_5359_, 5, v___x_5358_);
return v___x_5359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_5360_; lean_object* v___x_5361_; 
v___x_5360_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4);
v___x_5361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5361_, 0, v___x_5360_);
lean_ctor_set(v___x_5361_, 1, v___x_5360_);
lean_ctor_set(v___x_5361_, 2, v___x_5360_);
lean_ctor_set(v___x_5361_, 3, v___x_5360_);
lean_ctor_set(v___x_5361_, 4, v___x_5360_);
return v___x_5361_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_5366_; lean_object* v___x_5367_; 
v___x_5366_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12));
v___x_5367_ = l_Lean_stringToMessageData(v___x_5366_);
return v___x_5367_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_5368_; lean_object* v___x_5369_; 
v___x_5368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_5369_ = l_String_toRawSubstring_x27(v___x_5368_);
return v___x_5369_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17(void){
_start:
{
lean_object* v___x_5373_; 
v___x_5373_ = l_Array_mkArray0(lean_box(0));
return v___x_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(lean_object* v___x_5376_, lean_object* v___f_5377_, lean_object* v___x_5378_, lean_object* v___x_5379_, lean_object* v___x_5380_, lean_object* v___x_5381_, lean_object* v_declName_5382_, lean_object* v_stx_5383_, uint8_t v_attrKind_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
uint8_t v___x_5388_; uint8_t v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5388_ = 0;
v___x_5389_ = 1;
v___x_5390_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2);
v___x_5391_ = lean_unsigned_to_nat(0u);
v___x_5392_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_5393_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5);
v___x_5394_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6));
v___x_5395_ = lean_box(0);
lean_inc(v___x_5376_);
v___x_5396_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5396_, 0, v___x_5390_);
lean_ctor_set(v___x_5396_, 1, v___x_5376_);
lean_ctor_set(v___x_5396_, 2, v___x_5393_);
lean_ctor_set(v___x_5396_, 3, v___x_5394_);
lean_ctor_set(v___x_5396_, 4, v___x_5395_);
lean_ctor_set(v___x_5396_, 5, v___x_5391_);
lean_ctor_set(v___x_5396_, 6, v___x_5395_);
lean_ctor_set_uint8(v___x_5396_, sizeof(void*)*7, v___x_5388_);
lean_ctor_set_uint8(v___x_5396_, sizeof(void*)*7 + 1, v___x_5388_);
lean_ctor_set_uint8(v___x_5396_, sizeof(void*)*7 + 2, v___x_5388_);
lean_ctor_set_uint8(v___x_5396_, sizeof(void*)*7 + 3, v___x_5389_);
v___x_5397_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7);
v___x_5398_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8);
v___x_5399_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9);
v___x_5400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5397_);
lean_ctor_set(v___x_5400_, 1, v___x_5398_);
lean_ctor_set(v___x_5400_, 2, v___x_5376_);
lean_ctor_set(v___x_5400_, 3, v___x_5392_);
lean_ctor_set(v___x_5400_, 4, v___x_5399_);
v___x_5401_ = lean_st_mk_ref(v___x_5400_);
lean_inc(v_declName_5382_);
v___x_5402_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_declName_5382_, v___x_5388_, v___x_5396_, v___x_5401_, v___y_5385_, v___y_5386_);
if (lean_obj_tag(v___x_5402_) == 0)
{
lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
lean_dec_ref_known(v___x_5402_, 1);
v___x_5403_ = lean_unsigned_to_nat(1u);
v___x_5404_ = l_Lean_Syntax_getArg(v_stx_5383_, v___x_5403_);
lean_inc(v___x_5404_);
v___x_5405_ = l_Lean_getAttrParamOptPrio(v___x_5404_, v___y_5385_, v___y_5386_);
if (lean_obj_tag(v___x_5405_) == 0)
{
lean_object* v_a_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5503_; 
v_a_5406_ = lean_ctor_get(v___x_5405_, 0);
v_isSharedCheck_5503_ = !lean_is_exclusive(v___x_5405_);
if (v_isSharedCheck_5503_ == 0)
{
v___x_5408_ = v___x_5405_;
v_isShared_5409_ = v_isSharedCheck_5503_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_a_5406_);
lean_dec(v___x_5405_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5503_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v___x_5410_; lean_object* v___y_5417_; lean_object* v___y_5421_; lean_object* v___y_5422_; lean_object* v___y_5423_; lean_object* v___y_5424_; uint8_t v___y_5425_; lean_object* v___y_5439_; uint8_t v___y_5440_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
v___x_5410_ = lean_box(0);
v___x_5491_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
lean_inc(v_a_5406_);
lean_inc(v_declName_5382_);
v___x_5492_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(v___x_5491_, v_declName_5382_, v_a_5406_, v_attrKind_5384_, v___x_5396_, v___x_5401_, v___y_5385_, v___y_5386_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_dec(v_a_5406_);
lean_dec(v___x_5404_);
lean_dec_ref_known(v___x_5396_, 7);
lean_dec(v_declName_5382_);
lean_dec_ref(v___x_5381_);
lean_dec_ref(v___x_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___x_5378_);
lean_dec_ref(v___f_5377_);
v___y_5417_ = v___x_5492_;
goto v___jp_5416_;
}
else
{
lean_object* v_a_5493_; uint8_t v___y_5495_; uint8_t v___x_5501_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5493_);
v___x_5501_ = l_Lean_Exception_isInterrupt(v_a_5493_);
if (v___x_5501_ == 0)
{
uint8_t v___x_5502_; 
v___x_5502_ = l_Lean_Exception_isRuntime(v_a_5493_);
v___y_5495_ = v___x_5502_;
goto v___jp_5494_;
}
else
{
lean_dec(v_a_5493_);
v___y_5495_ = v___x_5501_;
goto v___jp_5494_;
}
v___jp_5494_:
{
if (v___y_5495_ == 0)
{
lean_object* v___x_5496_; lean_object* v___x_5497_; 
lean_dec_ref_known(v___x_5492_, 1);
v___x_5496_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_specAttr;
lean_inc(v_declName_5382_);
v___x_5497_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecExtension_addSpecTheoremFromConst(v___x_5496_, v_declName_5382_, v_a_5406_, v_attrKind_5384_, v___x_5396_, v___x_5401_, v___y_5385_, v___y_5386_);
if (lean_obj_tag(v___x_5497_) == 0)
{
lean_dec(v___x_5404_);
lean_dec_ref_known(v___x_5396_, 7);
lean_dec(v_declName_5382_);
lean_dec_ref(v___x_5381_);
lean_dec_ref(v___x_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___x_5378_);
lean_dec_ref(v___f_5377_);
v___y_5417_ = v___x_5497_;
goto v___jp_5416_;
}
else
{
lean_object* v_a_5498_; uint8_t v___x_5499_; 
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc(v_a_5498_);
v___x_5499_ = l_Lean_Exception_isInterrupt(v_a_5498_);
if (v___x_5499_ == 0)
{
uint8_t v___x_5500_; 
v___x_5500_ = l_Lean_Exception_isRuntime(v_a_5498_);
v___y_5439_ = v___x_5497_;
v___y_5440_ = v___x_5500_;
goto v___jp_5438_;
}
else
{
lean_dec(v_a_5498_);
v___y_5439_ = v___x_5497_;
v___y_5440_ = v___x_5499_;
goto v___jp_5438_;
}
}
}
else
{
lean_dec(v_a_5406_);
lean_dec(v___x_5404_);
lean_dec_ref_known(v___x_5396_, 7);
lean_dec(v_declName_5382_);
lean_dec_ref(v___x_5381_);
lean_dec_ref(v___x_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___x_5378_);
lean_dec_ref(v___f_5377_);
v___y_5417_ = v___x_5492_;
goto v___jp_5416_;
}
}
}
v___jp_5411_:
{
lean_object* v___x_5412_; lean_object* v___x_5414_; 
v___x_5412_ = lean_st_ref_get(v___x_5401_);
lean_dec(v___x_5401_);
lean_dec(v___x_5412_);
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 0, v___x_5410_);
v___x_5414_ = v___x_5408_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v___x_5410_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
v___jp_5416_:
{
if (lean_obj_tag(v___y_5417_) == 0)
{
lean_dec_ref_known(v___y_5417_, 1);
goto v___jp_5411_;
}
else
{
lean_del_object(v___x_5408_);
lean_dec(v___x_5401_);
return v___y_5417_;
}
}
v___jp_5418_:
{
lean_object* v___x_5419_; 
lean_inc(v___y_5386_);
lean_inc_ref(v___y_5385_);
lean_inc(v___x_5401_);
v___x_5419_ = lean_apply_6(v___f_5377_, v___x_5410_, v___x_5396_, v___x_5401_, v___y_5385_, v___y_5386_, lean_box(0));
v___y_5417_ = v___x_5419_;
goto v___jp_5416_;
}
v___jp_5420_:
{
if (v___y_5425_ == 0)
{
uint8_t v_hasTrace_5426_; 
lean_dec_ref(v___y_5422_);
v_hasTrace_5426_ = lean_ctor_get_uint8(v___y_5423_, sizeof(void*)*1);
if (v_hasTrace_5426_ == 0)
{
lean_dec_ref(v___y_5424_);
lean_dec_ref(v___x_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___x_5378_);
goto v___jp_5418_;
}
else
{
lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; uint8_t v___x_5431_; 
v___x_5427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_5428_ = l_Lean_Name_mkStr4(v___x_5378_, v___x_5379_, v___x_5380_, v___x_5427_);
v___x_5429_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11));
lean_inc(v___x_5428_);
v___x_5430_ = l_Lean_Name_append(v___x_5429_, v___x_5428_);
v___x_5431_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_5421_, v___y_5423_, v___x_5430_);
lean_dec(v___x_5430_);
if (v___x_5431_ == 0)
{
lean_dec(v___x_5428_);
lean_dec_ref(v___y_5424_);
goto v___jp_5418_;
}
else
{
lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5432_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13);
v___x_5433_ = l_Lean_Exception_toMessageData(v___y_5424_);
v___x_5434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5434_, 0, v___x_5432_);
lean_ctor_set(v___x_5434_, 1, v___x_5433_);
v___x_5435_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v___x_5428_, v___x_5434_, v___x_5396_, v___x_5401_, v___y_5385_, v___y_5386_);
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_object* v_a_5436_; lean_object* v___x_5437_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
lean_inc(v_a_5436_);
lean_dec_ref_known(v___x_5435_, 1);
lean_inc(v___y_5386_);
lean_inc_ref(v___y_5385_);
lean_inc(v___x_5401_);
v___x_5437_ = lean_apply_6(v___f_5377_, v_a_5436_, v___x_5396_, v___x_5401_, v___y_5385_, v___y_5386_, lean_box(0));
v___y_5417_ = v___x_5437_;
goto v___jp_5416_;
}
else
{
lean_dec_ref_known(v___x_5396_, 7);
lean_dec_ref(v___f_5377_);
v___y_5417_ = v___x_5435_;
goto v___jp_5416_;
}
}
}
}
else
{
lean_dec_ref(v___y_5424_);
lean_del_object(v___x_5408_);
lean_dec(v___x_5401_);
lean_dec_ref_known(v___x_5396_, 7);
lean_dec_ref(v___x_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___x_5378_);
lean_dec_ref(v___f_5377_);
return v___y_5422_;
}
}
v___jp_5438_:
{
if (v___y_5440_ == 0)
{
lean_object* v___x_5441_; lean_object* v___x_5442_; 
lean_dec_ref(v___y_5439_);
v___x_5441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_));
v___x_5442_ = l_Lean_getBuiltinAttributeImpl(v___x_5441_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_a_5443_; lean_object* v_options_5444_; lean_object* v_ref_5445_; lean_object* v_quotContext_5446_; lean_object* v_currMacroScope_5447_; lean_object* v_inheritedTraceOptions_5448_; lean_object* v_add_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5475_; 
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_a_5443_);
lean_dec_ref_known(v___x_5442_, 1);
v_options_5444_ = lean_ctor_get(v___y_5385_, 2);
v_ref_5445_ = lean_ctor_get(v___y_5385_, 5);
v_quotContext_5446_ = lean_ctor_get(v___y_5385_, 10);
v_currMacroScope_5447_ = lean_ctor_get(v___y_5385_, 11);
v_inheritedTraceOptions_5448_ = lean_ctor_get(v___y_5385_, 13);
v_add_5449_ = lean_ctor_get(v_a_5443_, 1);
v_isSharedCheck_5475_ = !lean_is_exclusive(v_a_5443_);
if (v_isSharedCheck_5475_ == 0)
{
lean_object* v_unused_5476_; lean_object* v_unused_5477_; 
v_unused_5476_ = lean_ctor_get(v_a_5443_, 2);
lean_dec(v_unused_5476_);
v_unused_5477_ = lean_ctor_get(v_a_5443_, 0);
lean_dec(v_unused_5477_);
v___x_5451_ = v_a_5443_;
v_isShared_5452_ = v_isSharedCheck_5475_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_add_5449_);
lean_dec(v_a_5443_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5475_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5461_; 
v___x_5453_ = l_Lean_SourceInfo_fromRef(v_ref_5445_, v___y_5440_);
v___x_5454_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14);
lean_inc(v_currMacroScope_5447_);
lean_inc(v_quotContext_5446_);
v___x_5455_ = l_Lean_addMacroScope(v_quotContext_5446_, v___x_5441_, v_currMacroScope_5447_);
v___x_5456_ = lean_box(0);
lean_inc_n(v___x_5453_, 2);
v___x_5457_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5457_, 0, v___x_5453_);
lean_ctor_set(v___x_5457_, 1, v___x_5454_);
lean_ctor_set(v___x_5457_, 2, v___x_5455_);
lean_ctor_set(v___x_5457_, 3, v___x_5456_);
v___x_5458_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16));
v___x_5459_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17);
if (v_isShared_5452_ == 0)
{
lean_ctor_set_tag(v___x_5451_, 1);
lean_ctor_set(v___x_5451_, 2, v___x_5459_);
lean_ctor_set(v___x_5451_, 1, v___x_5458_);
lean_ctor_set(v___x_5451_, 0, v___x_5453_);
v___x_5461_ = v___x_5451_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v___x_5453_);
lean_ctor_set(v_reuseFailAlloc_5474_, 1, v___x_5458_);
lean_ctor_set(v_reuseFailAlloc_5474_, 2, v___x_5459_);
v___x_5461_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; 
v___x_5462_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18));
v___x_5463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_));
v___x_5464_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19));
v___x_5465_ = l_Lean_Name_mkStr4(v___x_5381_, v___x_5462_, v___x_5463_, v___x_5464_);
v___x_5466_ = l_Lean_Syntax_node2(v___x_5453_, v___x_5465_, v___x_5457_, v___x_5461_);
v___x_5467_ = lean_unsigned_to_nat(3u);
v___x_5468_ = l_Lean_Syntax_setArg(v___x_5466_, v___x_5467_, v___x_5404_);
v___x_5469_ = lean_box(v_attrKind_5384_);
lean_inc(v___y_5386_);
lean_inc_ref(v___y_5385_);
v___x_5470_ = lean_apply_6(v_add_5449_, v_declName_5382_, v___x_5468_, v___x_5469_, v___y_5385_, v___y_5386_, lean_box(0));
if (lean_obj_tag(v___x_5470_) == 0)
{
lean_dec_ref_known(v___x_5470_, 1);
lean_dec_ref_known(v___x_5396_, 7);
lean_dec_ref(v___x_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___x_5378_);
lean_dec_ref(v___f_5377_);
goto v___jp_5411_;
}
else
{
lean_object* v_a_5471_; uint8_t v___x_5472_; 
v_a_5471_ = lean_ctor_get(v___x_5470_, 0);
lean_inc(v_a_5471_);
v___x_5472_ = l_Lean_Exception_isInterrupt(v_a_5471_);
if (v___x_5472_ == 0)
{
uint8_t v___x_5473_; 
lean_inc(v_a_5471_);
v___x_5473_ = l_Lean_Exception_isRuntime(v_a_5471_);
v___y_5421_ = v_inheritedTraceOptions_5448_;
v___y_5422_ = v___x_5470_;
v___y_5423_ = v_options_5444_;
v___y_5424_ = v_a_5471_;
v___y_5425_ = v___x_5473_;
goto v___jp_5420_;
}
else
{
v___y_5421_ = v_inheritedTraceOptions_5448_;
v___y_5422_ = v___x_5470_;
v___y_5423_ = v_options_5444_;
v___y_5424_ = v_a_5471_;
v___y_5425_ = v___x_5472_;
goto v___jp_5420_;
}
}
}
}
}
else
{
lean_object* v_a_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5490_; 
lean_del_object(v___x_5408_);
lean_dec(v___x_5404_);
lean_dec(v___x_5401_);
lean_dec_ref_known(v___x_5396_, 7);
lean_dec(v_declName_5382_);
lean_dec_ref(v___x_5381_);
lean_dec_ref(v___x_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___x_5378_);
lean_dec_ref(v___f_5377_);
v_a_5478_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5480_ = v___x_5442_;
v_isShared_5481_ = v_isSharedCheck_5490_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_a_5478_);
lean_dec(v___x_5442_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5490_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v_ref_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5488_; 
v_ref_5482_ = lean_ctor_get(v___y_5385_, 5);
v___x_5483_ = lean_io_error_to_string(v_a_5478_);
v___x_5484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5483_);
v___x_5485_ = l_Lean_MessageData_ofFormat(v___x_5484_);
lean_inc(v_ref_5482_);
v___x_5486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5486_, 0, v_ref_5482_);
lean_ctor_set(v___x_5486_, 1, v___x_5485_);
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 0, v___x_5486_);
v___x_5488_ = v___x_5480_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v___x_5486_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
else
{
lean_dec(v___x_5404_);
lean_dec_ref_known(v___x_5396_, 7);
lean_dec(v_declName_5382_);
lean_dec_ref(v___x_5381_);
lean_dec_ref(v___x_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___x_5378_);
lean_dec_ref(v___f_5377_);
v___y_5417_ = v___y_5439_;
goto v___jp_5416_;
}
}
}
}
else
{
lean_object* v_a_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5511_; 
lean_dec(v___x_5404_);
lean_dec(v___x_5401_);
lean_dec_ref_known(v___x_5396_, 7);
lean_dec(v_declName_5382_);
lean_dec_ref(v___x_5381_);
lean_dec_ref(v___x_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___x_5378_);
lean_dec_ref(v___f_5377_);
v_a_5504_ = lean_ctor_get(v___x_5405_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___x_5405_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5506_ = v___x_5405_;
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_a_5504_);
lean_dec(v___x_5405_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5509_; 
if (v_isShared_5507_ == 0)
{
v___x_5509_ = v___x_5506_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5504_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
}
}
else
{
lean_object* v_a_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5519_; 
lean_dec(v___x_5401_);
lean_dec_ref_known(v___x_5396_, 7);
lean_dec(v_declName_5382_);
lean_dec_ref(v___x_5381_);
lean_dec_ref(v___x_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___x_5378_);
lean_dec_ref(v___f_5377_);
v_a_5512_ = lean_ctor_get(v___x_5402_, 0);
v_isSharedCheck_5519_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5519_ == 0)
{
v___x_5514_ = v___x_5402_;
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_a_5512_);
lean_dec(v___x_5402_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5517_; 
if (v_isShared_5515_ == 0)
{
v___x_5517_ = v___x_5514_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5512_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed(lean_object* v___x_5520_, lean_object* v___f_5521_, lean_object* v___x_5522_, lean_object* v___x_5523_, lean_object* v___x_5524_, lean_object* v___x_5525_, lean_object* v_declName_5526_, lean_object* v_stx_5527_, lean_object* v_attrKind_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_){
_start:
{
uint8_t v_attrKind_boxed_5532_; lean_object* v_res_5533_; 
v_attrKind_boxed_5532_ = lean_unbox(v_attrKind_5528_);
v_res_5533_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(v___x_5520_, v___f_5521_, v___x_5522_, v___x_5523_, v___x_5524_, v___x_5525_, v_declName_5526_, v_stx_5527_, v_attrKind_boxed_5532_, v___y_5529_, v___y_5530_);
lean_dec(v___y_5530_);
lean_dec_ref(v___y_5529_);
lean_dec(v_stx_5527_);
return v_res_5533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(lean_object* v_msgData_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_){
_start:
{
lean_object* v___x_5538_; lean_object* v_env_5539_; lean_object* v_options_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; 
v___x_5538_ = lean_st_ref_get(v___y_5536_);
v_env_5539_ = lean_ctor_get(v___x_5538_, 0);
lean_inc_ref(v_env_5539_);
lean_dec(v___x_5538_);
v_options_5540_ = lean_ctor_get(v___y_5535_, 2);
v___x_5541_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_5542_ = lean_unsigned_to_nat(32u);
v___x_5543_ = lean_mk_empty_array_with_capacity(v___x_5542_);
lean_dec_ref(v___x_5543_);
v___x_5544_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
lean_inc_ref(v_options_5540_);
v___x_5545_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5545_, 0, v_env_5539_);
lean_ctor_set(v___x_5545_, 1, v___x_5541_);
lean_ctor_set(v___x_5545_, 2, v___x_5544_);
lean_ctor_set(v___x_5545_, 3, v_options_5540_);
v___x_5546_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5545_);
lean_ctor_set(v___x_5546_, 1, v_msgData_5534_);
v___x_5547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5547_, 0, v___x_5546_);
return v___x_5547_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2___boxed(lean_object* v_msgData_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_){
_start:
{
lean_object* v_res_5552_; 
v_res_5552_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msgData_5548_, v___y_5549_, v___y_5550_);
lean_dec(v___y_5550_);
lean_dec_ref(v___y_5549_);
return v_res_5552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(lean_object* v_msg_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_){
_start:
{
lean_object* v_ref_5557_; lean_object* v___x_5558_; lean_object* v_a_5559_; lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5567_; 
v_ref_5557_ = lean_ctor_get(v___y_5554_, 5);
v___x_5558_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msg_5553_, v___y_5554_, v___y_5555_);
v_a_5559_ = lean_ctor_get(v___x_5558_, 0);
v_isSharedCheck_5567_ = !lean_is_exclusive(v___x_5558_);
if (v_isSharedCheck_5567_ == 0)
{
v___x_5561_ = v___x_5558_;
v_isShared_5562_ = v_isSharedCheck_5567_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_a_5559_);
lean_dec(v___x_5558_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5567_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5563_; lean_object* v___x_5565_; 
lean_inc(v_ref_5557_);
v___x_5563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5563_, 0, v_ref_5557_);
lean_ctor_set(v___x_5563_, 1, v_a_5559_);
if (v_isShared_5562_ == 0)
{
lean_ctor_set_tag(v___x_5561_, 1);
lean_ctor_set(v___x_5561_, 0, v___x_5563_);
v___x_5565_ = v___x_5561_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v___x_5563_);
v___x_5565_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
return v___x_5565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg___boxed(lean_object* v_msg_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_){
_start:
{
lean_object* v_res_5572_; 
v_res_5572_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v_msg_5568_, v___y_5569_, v___y_5570_);
lean_dec(v___y_5570_);
lean_dec_ref(v___y_5569_);
return v_res_5572_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_5574_; lean_object* v___x_5575_; 
v___x_5574_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0));
v___x_5575_ = l_Lean_stringToMessageData(v___x_5574_);
return v___x_5575_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_5577_; lean_object* v___x_5578_; 
v___x_5577_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2));
v___x_5578_ = l_Lean_stringToMessageData(v___x_5577_);
return v___x_5578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(lean_object* v___x_5579_, lean_object* v_decl_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_){
_start:
{
lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_5584_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1);
v___x_5585_ = l_Lean_MessageData_ofName(v___x_5579_);
v___x_5586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5586_, 0, v___x_5584_);
lean_ctor_set(v___x_5586_, 1, v___x_5585_);
v___x_5587_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3);
v___x_5588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5588_, 0, v___x_5586_);
lean_ctor_set(v___x_5588_, 1, v___x_5587_);
v___x_5589_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v___x_5588_, v___y_5581_, v___y_5582_);
return v___x_5589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed(lean_object* v___x_5590_, lean_object* v_decl_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_){
_start:
{
lean_object* v_res_5595_; 
v_res_5595_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(v___x_5590_, v_decl_5591_, v___y_5592_, v___y_5593_);
lean_dec(v___y_5593_);
lean_dec_ref(v___y_5592_);
lean_dec(v_decl_5591_);
return v_res_5595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(lean_object* v_00_u03b1_5628_, lean_object* v_msg_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_){
_start:
{
lean_object* v___x_5633_; 
v___x_5633_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(v_msg_5629_, v___y_5630_, v___y_5631_);
return v___x_5633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___boxed(lean_object* v_00_u03b1_5634_, lean_object* v_msg_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(v_00_u03b1_5634_, v_msg_5635_, v___y_5636_, v___y_5637_);
lean_dec(v___y_5637_);
lean_dec_ref(v___y_5636_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3903886647____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5641_; lean_object* v___x_5642_; 
v___x_5641_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr));
v___x_5642_ = l_Lean_registerBuiltinAttribute(v___x_5641_);
return v___x_5642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3903886647____hygCtx___hyg_2____boxed(lean_object* v_a_5643_){
_start:
{
lean_object* v_res_5644_; 
v_res_5644_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3903886647____hygCtx___hyg_2_();
return v_res_5644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(lean_object* v_x_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_){
_start:
{
lean_object* v___x_5649_; lean_object* v___x_5650_; 
v___x_5649_ = lean_box(0);
v___x_5650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5649_);
return v___x_5650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object* v_x_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_){
_start:
{
lean_object* v_res_5655_; 
v_res_5655_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(v_x_5651_, v___y_5652_, v___y_5653_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
lean_dec(v_x_5651_);
return v_res_5655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; uint8_t v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; 
v___f_5670_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_5671_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_5672_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_5673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_));
v___x_5674_ = 0;
v___x_5675_ = lean_box(2);
v___x_5676_ = l_Lean_registerTagAttribute(v___x_5671_, v___x_5672_, v___f_5670_, v___x_5673_, v___x_5674_, v___x_5675_);
return v___x_5676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(lean_object* v_a_5677_){
_start:
{
lean_object* v_res_5678_; 
v_res_5678_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
return v_res_5678_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(lean_object* v_env_5679_, lean_object* v_ty_5680_){
_start:
{
lean_object* v___x_5681_; 
v___x_5681_ = l_Lean_Expr_getAppFn(v_ty_5680_);
if (lean_obj_tag(v___x_5681_) == 4)
{
lean_object* v_declName_5682_; lean_object* v___x_5683_; uint8_t v___x_5684_; 
v_declName_5682_ = lean_ctor_get(v___x_5681_, 0);
lean_inc(v_declName_5682_);
lean_dec_ref_known(v___x_5681_, 2);
v___x_5683_ = l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr;
v___x_5684_ = l_Lean_TagAttribute_hasTag(v___x_5683_, v_env_5679_, v_declName_5682_);
return v___x_5684_;
}
else
{
uint8_t v___x_5685_; 
lean_dec_ref(v___x_5681_);
lean_dec_ref(v_env_5679_);
v___x_5685_ = 0;
return v___x_5685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType___boxed(lean_object* v_env_5686_, lean_object* v_ty_5687_){
_start:
{
uint8_t v_res_5688_; lean_object* v_r_5689_; 
v_res_5688_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v_env_5686_, v_ty_5687_);
lean_dec_ref(v_ty_5687_);
v_r_5689_ = lean_box(v_res_5688_);
return v_r_5689_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
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
l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheoremKind_default = _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheoremKind_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheoremKind_default);
l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheoremKind = _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheoremKind();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheoremKind);
l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default = _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem_default);
l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem = _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorem);
l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default = _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default);
l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems = _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems);
l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt = _init_l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecExt);
res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486626____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Do_Internal_SpecAttr_specAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_SpecAttr_specAttr);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3903886647____hygCtx___hyg_2_();
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
lean_object* initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
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
