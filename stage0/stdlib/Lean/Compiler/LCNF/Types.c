// Lean compiler output
// Module: Lean.Compiler.LCNF.Types
// Imports: public import Lean.Compiler.BorrowedAnnotation public import Lean.Meta.InferType import Init.Omega import Lean.OriginalConstKind
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* l_Lean_markBorrowed(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_getOriginalConstKind_x3f(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isClass(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_term_u25fe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_term_u25fe___closed__0 = (const lean_object*)&l_Lean_Compiler_term_u25fe___closed__0_value;
static const lean_string_object l_Lean_Compiler_term_u25fe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_term_u25fe___closed__1 = (const lean_object*)&l_Lean_Compiler_term_u25fe___closed__1_value;
static const lean_string_object l_Lean_Compiler_term_u25fe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term◾"};
static const lean_object* l_Lean_Compiler_term_u25fe___closed__2 = (const lean_object*)&l_Lean_Compiler_term_u25fe___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_term_u25fe___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_term_u25fe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_term_u25fe___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_term_u25fe___closed__3_value_aux_0),((lean_object*)&l_Lean_Compiler_term_u25fe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_term_u25fe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_term_u25fe___closed__3_value_aux_1),((lean_object*)&l_Lean_Compiler_term_u25fe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(84, 129, 89, 34, 159, 17, 200, 73)}};
static const lean_object* l_Lean_Compiler_term_u25fe___closed__3 = (const lean_object*)&l_Lean_Compiler_term_u25fe___closed__3_value;
static const lean_string_object l_Lean_Compiler_term_u25fe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "◾"};
static const lean_object* l_Lean_Compiler_term_u25fe___closed__4 = (const lean_object*)&l_Lean_Compiler_term_u25fe___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_term_u25fe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Compiler_term_u25fe___closed__4_value)}};
static const lean_object* l_Lean_Compiler_term_u25fe___closed__5 = (const lean_object*)&l_Lean_Compiler_term_u25fe___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_term_u25fe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_term_u25fe___closed__3_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Compiler_term_u25fe___closed__5_value)}};
static const lean_object* l_Lean_Compiler_term_u25fe___closed__6 = (const lean_object*)&l_Lean_Compiler_term_u25fe___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_term_u25fe = (const lean_object*)&l_Lean_Compiler_term_u25fe___closed__6_value;
static const lean_string_object l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__0 = (const lean_object*)&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__0_value;
static lean_once_cell_t l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1;
static const lean_ctor_object l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 218, 234, 194, 194, 57, 75, 5)}};
static const lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2 = (const lean_object*)&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2_value;
static const lean_ctor_object l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__3 = (const lean_object*)&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__3_value;
static const lean_ctor_object l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__4 = (const lean_object*)&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__0 = (const lean_object*)&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__0_value;
static const lean_ctor_object l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__1 = (const lean_object*)&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_erasedExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_erasedExpr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_erasedExpr;
static const lean_string_object l_Lean_Compiler_LCNF_anyExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lcAny"};
static const lean_object* l_Lean_Compiler_LCNF_anyExpr___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_anyExpr___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_anyExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_anyExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 177, 139, 0, 112, 130, 192, 131)}};
static const lean_object* l_Lean_Compiler_LCNF_anyExpr___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_anyExpr___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_anyExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_anyExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_anyExpr;
static const lean_string_object l_Lean_Expr_isVoid___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lcVoid"};
static const lean_object* l_Lean_Expr_isVoid___closed__0 = (const lean_object*)&l_Lean_Expr_isVoid___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isVoid___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isVoid___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 180, 59, 167, 252, 217, 37, 174)}};
static const lean_object* l_Lean_Expr_isVoid___closed__1 = (const lean_object*)&l_Lean_Expr_isVoid___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isVoid(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isVoid___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isErased(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isErased___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAny(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAny___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPropFormerTypeQuick(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerTypeQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0;
static const lean_string_object l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Subtype"};
static const lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Void"};
static const lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nonemptyType"};
static const lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "internal compiler error: private in public"};
static const lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0 = (const lean_object*)&l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0_value;
static lean_once_cell_t l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1;
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_toLCNFType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "locally inferred compilation type"};
static const lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toLCNFType___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toLCNFType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_toLCNFType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "\ndiffers from type"};
static const lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_toLCNFType___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toLCNFType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_toLCNFType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 147, .m_capacity = 147, .m_length = 146, .m_data = "\nthat would be inferred in other modules. This usually means that a type `def` involved with the mentioned declarations needs to be `@[expose]`d. "};
static const lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_toLCNFType___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toLCNFType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_toLCNFType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Compilation failed, "};
static const lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_toLCNFType___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toLCNFType___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_toLCNFType___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "This is a current compiler limitation for `module`s that may be lifted in the future."};
static const lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_toLCNFType___closed__8_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toLCNFType___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__9;
static const lean_array_object l_Lean_Compiler_LCNF_toLCNFType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_toLCNFType___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_toLCNFType___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 178, .m_capacity = 178, .m_length = 177, .m_data = "locally inferred compilation type differs from type that would be inferred in other modules. Some of the following definitions may need to be `@[expose]`d to fix this mismatch: "};
static const lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_toLCNFType___closed__11_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toLCNFType___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__12;
static lean_once_cell_t l_Lean_Compiler_LCNF_toLCNFType___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__13;
static const lean_string_object l_Lean_Compiler_LCNF_toLCNFType___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_toLCNFType___closed__14_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toLCNFType___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toLCNFType___closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTypeFormerType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid instantiateForall, too many parameters"};
static const lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPredicateType___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_maybeTypeFormerType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_maybeTypeFormerType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkBoxedName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l_Lean_Compiler_LCNF_mkBoxedName___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkBoxedName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isBoxedName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isBoxedName___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_ImpureType_float___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_float___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_float___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ImpureType_float___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ImpureType_float___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 69, 114, 85, 163, 177, 220, 67)}};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_float___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_float___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_float___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_float___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_float;
static const lean_string_object l_Lean_Compiler_LCNF_ImpureType_float32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_float32___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_float32___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ImpureType_float32___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ImpureType_float32___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 232, 182, 48, 64, 193, 160, 231)}};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_float32___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_float32___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_float32___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_float32___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_float32;
static const lean_string_object l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_uint8;
static const lean_string_object l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_uint16;
static const lean_string_object l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_uint32;
static const lean_string_object l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_uint64;
static const lean_string_object l_Lean_Compiler_LCNF_ImpureType_usize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_usize___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_usize___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ImpureType_usize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ImpureType_usize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_usize___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_usize___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_usize___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_usize___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_usize;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_erased___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_erased___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_erased;
static const lean_string_object l_Lean_Compiler_LCNF_ImpureType_object___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_object___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_object___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ImpureType_object___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ImpureType_object___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 235, 44, 74, 242, 121, 239, 90)}};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_object___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_object___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_object___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_object;
static const lean_string_object l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_tobject;
static const lean_string_object l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 57, 252, 162, 142, 133, 51, 193)}};
static const lean_object* l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_tagged;
static lean_once_cell_t l_Lean_Compiler_LCNF_ImpureType_void___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ImpureType_void___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_void;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed___boxed(lean_object*);
static lean_object* _init_l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__0));
v___x_18_ = l_String_toRawSubstring_x27(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1(lean_object* v_x_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = ((lean_object*)(l_Lean_Compiler_term_u25fe___closed__3));
v___x_31_ = l_Lean_Syntax_isOfKind(v_x_27_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_box(1);
v___x_33_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v_a_29_);
return v___x_33_;
}
else
{
lean_object* v_quotContext_34_; lean_object* v_currMacroScope_35_; lean_object* v_ref_36_; uint8_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_quotContext_34_ = lean_ctor_get(v_a_28_, 1);
v_currMacroScope_35_ = lean_ctor_get(v_a_28_, 2);
v_ref_36_ = lean_ctor_get(v_a_28_, 5);
v___x_37_ = 0;
v___x_38_ = l_Lean_SourceInfo_fromRef(v_ref_36_, v___x_37_);
v___x_39_ = lean_obj_once(&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1, &l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1_once, _init_l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1);
v___x_40_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
lean_inc(v_currMacroScope_35_);
lean_inc(v_quotContext_34_);
v___x_41_ = l_Lean_addMacroScope(v_quotContext_34_, v___x_40_, v_currMacroScope_35_);
v___x_42_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__4));
v___x_43_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_43_, 0, v___x_38_);
lean_ctor_set(v___x_43_, 1, v___x_39_);
lean_ctor_set(v___x_43_, 2, v___x_41_);
lean_ctor_set(v___x_43_, 3, v___x_42_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v_a_29_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___boxed(lean_object* v_x_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1(v_x_45_, v_a_46_, v_a_47_);
lean_dec_ref(v_a_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1(lean_object* v_x_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__1));
lean_inc(v_x_52_);
v___x_56_ = l_Lean_Syntax_isOfKind(v_x_52_, v___x_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_x_52_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v_a_54_);
return v___x_58_;
}
else
{
lean_object* v_ref_59_; uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_ref_59_ = l_Lean_replaceRef(v_x_52_, v_a_53_);
lean_dec(v_x_52_);
v___x_60_ = 0;
v___x_61_ = l_Lean_SourceInfo_fromRef(v_ref_59_, v___x_60_);
lean_dec(v_ref_59_);
v___x_62_ = ((lean_object*)(l_Lean_Compiler_term_u25fe___closed__3));
v___x_63_ = ((lean_object*)(l_Lean_Compiler_term_u25fe___closed__4));
lean_inc(v___x_61_);
v___x_64_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_61_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = l_Lean_Syntax_node1(v___x_61_, v___x_62_, v___x_64_);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v_a_54_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___boxed(lean_object* v_x_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1(v_x_67_, v_a_68_, v_a_69_);
lean_dec(v_a_68_);
return v_res_70_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_erasedExpr___closed__0(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_box(0);
v___x_72_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_73_ = l_Lean_mkConst(v___x_72_, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_erasedExpr(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Lean_Compiler_LCNF_erasedExpr___closed__0, &l_Lean_Compiler_LCNF_erasedExpr___closed__0_once, _init_l_Lean_Compiler_LCNF_erasedExpr___closed__0);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_anyExpr___closed__2(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_box(0);
v___x_79_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyExpr___closed__1));
v___x_80_ = l_Lean_mkConst(v___x_79_, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_anyExpr(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
return v___x_81_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isVoid(lean_object* v_e_85_){
_start:
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_87_ = l_Lean_Expr_isAppOf(v_e_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isVoid___boxed(lean_object* v_e_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lean_Expr_isVoid(v_e_88_);
lean_dec_ref(v_e_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isErased(lean_object* v_e_91_){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_93_ = l_Lean_Expr_isAppOf(v_e_91_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isErased___boxed(lean_object* v_e_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Lean_Expr_isErased(v_e_94_);
lean_dec_ref(v_e_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAny(lean_object* v_e_97_){
_start:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyExpr___closed__1));
v___x_99_ = l_Lean_Expr_isAppOf(v_e_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAny___boxed(lean_object* v_e_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Lean_Expr_isAny(v_e_100_);
lean_dec_ref(v_e_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPropFormerTypeQuick(lean_object* v_x_103_){
_start:
{
switch(lean_obj_tag(v_x_103_))
{
case 7:
{
lean_object* v_body_104_; 
v_body_104_ = lean_ctor_get(v_x_103_, 2);
v_x_103_ = v_body_104_;
goto _start;
}
case 3:
{
lean_object* v_u_106_; 
v_u_106_ = lean_ctor_get(v_x_103_, 0);
if (lean_obj_tag(v_u_106_) == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 1;
return v___x_107_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
default: 
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerTypeQuick___boxed(lean_object* v_x_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_x_110_);
lean_dec_ref(v_x_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(lean_object* v_k_113_, lean_object* v_b_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___x_120_; 
lean_inc(v___y_118_);
lean_inc_ref(v___y_117_);
lean_inc(v___y_116_);
lean_inc_ref(v___y_115_);
v___x_120_ = lean_apply_6(v_k_113_, v_b_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, lean_box(0));
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_121_, lean_object* v_b_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(v_k_121_, v_b_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(lean_object* v_name_129_, uint8_t v_bi_130_, lean_object* v_type_131_, lean_object* v_k_132_, uint8_t v_kind_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___f_139_; lean_object* v___x_140_; 
v___f_139_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_139_, 0, v_k_132_);
v___x_140_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_129_, v_bi_130_, v_type_131_, v___f_139_, v_kind_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_a_149_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_140_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_140_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___boxed(lean_object* v_name_157_, lean_object* v_bi_158_, lean_object* v_type_159_, lean_object* v_k_160_, lean_object* v_kind_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
uint8_t v_bi_boxed_167_; uint8_t v_kind_boxed_168_; lean_object* v_res_169_; 
v_bi_boxed_167_ = lean_unbox(v_bi_158_);
v_kind_boxed_168_ = lean_unbox(v_kind_161_);
v_res_169_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_name_157_, v_bi_boxed_167_, v_type_159_, v_k_160_, v_kind_boxed_168_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0(lean_object* v_00_u03b1_170_, lean_object* v_name_171_, uint8_t v_bi_172_, lean_object* v_type_173_, lean_object* v_k_174_, uint8_t v_kind_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_name_171_, v_bi_172_, v_type_173_, v_k_174_, v_kind_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___boxed(lean_object* v_00_u03b1_182_, lean_object* v_name_183_, lean_object* v_bi_184_, lean_object* v_type_185_, lean_object* v_k_186_, lean_object* v_kind_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
uint8_t v_bi_boxed_193_; uint8_t v_kind_boxed_194_; lean_object* v_res_195_; 
v_bi_boxed_193_ = lean_unbox(v_bi_184_);
v_kind_boxed_194_ = lean_unbox(v_kind_187_);
v_res_195_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0(v_00_u03b1_182_, v_name_183_, v_bi_boxed_193_, v_type_185_, v_k_186_, v_kind_boxed_194_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed(lean_object* v_xs_198_, lean_object* v_body_199_, lean_object* v_x_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(v_xs_198_, v_body_199_, v_x_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(lean_object* v_type_207_, lean_object* v_xs_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; 
switch(lean_obj_tag(v_type_207_))
{
case 3:
{
lean_object* v_u_241_; 
v_u_241_ = lean_ctor_get(v_type_207_, 0);
if (lean_obj_tag(v_u_241_) == 0)
{
lean_dec_ref_known(v_type_207_, 1);
lean_dec_ref(v_xs_208_);
goto v___jp_214_;
}
else
{
v___y_223_ = v_a_209_;
v___y_224_ = v_a_210_;
v___y_225_ = v_a_211_;
v___y_226_ = v_a_212_;
goto v___jp_222_;
}
}
case 7:
{
lean_object* v_binderName_242_; lean_object* v_binderType_243_; lean_object* v_body_244_; uint8_t v_binderInfo_245_; lean_object* v___f_246_; lean_object* v___x_247_; uint8_t v___x_248_; lean_object* v___x_249_; 
v_binderName_242_ = lean_ctor_get(v_type_207_, 0);
lean_inc(v_binderName_242_);
v_binderType_243_ = lean_ctor_get(v_type_207_, 1);
lean_inc_ref(v_binderType_243_);
v_body_244_ = lean_ctor_get(v_type_207_, 2);
lean_inc_ref(v_body_244_);
v_binderInfo_245_ = lean_ctor_get_uint8(v_type_207_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_207_, 3);
lean_inc_ref(v_xs_208_);
v___f_246_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_246_, 0, v_xs_208_);
lean_closure_set(v___f_246_, 1, v_body_244_);
v___x_247_ = lean_expr_instantiate_rev(v_binderType_243_, v_xs_208_);
lean_dec_ref(v_xs_208_);
lean_dec_ref(v_binderType_243_);
v___x_248_ = 0;
v___x_249_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_242_, v_binderInfo_245_, v___x_247_, v___f_246_, v___x_248_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
return v___x_249_;
}
default: 
{
v___y_223_ = v_a_209_;
v___y_224_ = v_a_210_;
v___y_225_ = v_a_211_;
v___y_226_ = v_a_212_;
goto v___jp_222_;
}
}
v___jp_214_:
{
uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = 1;
v___x_216_ = lean_box(v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
v___jp_218_:
{
uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = 0;
v___x_220_ = lean_box(v___x_219_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
v___jp_222_:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_expr_instantiate_rev(v_type_207_, v_xs_208_);
lean_dec_ref(v_xs_208_);
lean_dec_ref(v_type_207_);
v___x_228_ = l_Lean_Meta_whnfD(v___x_227_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
switch(lean_obj_tag(v_a_229_))
{
case 3:
{
lean_object* v_u_230_; 
v_u_230_ = lean_ctor_get(v_a_229_, 0);
lean_inc(v_u_230_);
lean_dec_ref_known(v_a_229_, 1);
if (lean_obj_tag(v_u_230_) == 0)
{
goto v___jp_214_;
}
else
{
lean_dec(v_u_230_);
goto v___jp_218_;
}
}
case 7:
{
lean_object* v___x_231_; 
v___x_231_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v_type_207_ = v_a_229_;
v_xs_208_ = v___x_231_;
v_a_209_ = v___y_223_;
v_a_210_ = v___y_224_;
v_a_211_ = v___y_225_;
v_a_212_ = v___y_226_;
goto _start;
}
default: 
{
lean_dec(v_a_229_);
goto v___jp_218_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_a_233_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_228_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_228_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(lean_object* v_xs_250_, lean_object* v_body_251_, lean_object* v_x_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_array_push(v_xs_250_, v_x_252_);
v___x_259_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_body_251_, v___x_258_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___boxed(lean_object* v_type_260_, lean_object* v_xs_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_260_, v_xs_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType(lean_object* v_type_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_type_268_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_276_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_268_, v___x_275_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec_ref(v_type_268_);
v___x_277_ = lean_box(v___x_274_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType___boxed(lean_object* v_type_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Compiler_LCNF_isPropFormerType(v_type_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer(lean_object* v_e_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_292_; 
lean_inc(v_a_290_);
lean_inc_ref(v_a_289_);
lean_inc(v_a_288_);
lean_inc_ref(v_a_287_);
v___x_292_ = lean_infer_type(v_e_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_292_, 1);
v___x_294_ = l_Lean_Compiler_LCNF_isPropFormerType(v_a_293_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
return v___x_294_;
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
v_a_295_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_292_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_292_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer___boxed(lean_object* v_e_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Compiler_LCNF_isPropFormer(v_e_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(lean_object* v_type_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___y_317_; lean_object* v___x_337_; uint8_t v_transparency_338_; uint8_t v___x_339_; uint8_t v___x_340_; 
v___x_337_ = l_Lean_Meta_Context_config(v_a_311_);
v_transparency_338_ = lean_ctor_get_uint8(v___x_337_, 9);
lean_dec_ref(v___x_337_);
v___x_339_ = 0;
v___x_340_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v_keyedConfig_341_; uint8_t v_trackZetaDelta_342_; lean_object* v_zetaDeltaSet_343_; lean_object* v_lctx_344_; lean_object* v_localInstances_345_; lean_object* v_defEqCtx_x3f_346_; lean_object* v_synthPendingDepth_347_; lean_object* v_customCanUnfoldPredicate_x3f_348_; uint8_t v_univApprox_349_; uint8_t v_inTypeClassResolution_350_; uint8_t v_cacheInferType_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_keyedConfig_341_ = lean_ctor_get(v_a_311_, 0);
v_trackZetaDelta_342_ = lean_ctor_get_uint8(v_a_311_, sizeof(void*)*7);
v_zetaDeltaSet_343_ = lean_ctor_get(v_a_311_, 1);
v_lctx_344_ = lean_ctor_get(v_a_311_, 2);
v_localInstances_345_ = lean_ctor_get(v_a_311_, 3);
v_defEqCtx_x3f_346_ = lean_ctor_get(v_a_311_, 4);
v_synthPendingDepth_347_ = lean_ctor_get(v_a_311_, 5);
v_customCanUnfoldPredicate_x3f_348_ = lean_ctor_get(v_a_311_, 6);
v_univApprox_349_ = lean_ctor_get_uint8(v_a_311_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_350_ = lean_ctor_get_uint8(v_a_311_, sizeof(void*)*7 + 2);
v_cacheInferType_351_ = lean_ctor_get_uint8(v_a_311_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_341_);
v___x_352_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_339_, v_keyedConfig_341_);
lean_inc(v_customCanUnfoldPredicate_x3f_348_);
lean_inc(v_synthPendingDepth_347_);
lean_inc(v_defEqCtx_x3f_346_);
lean_inc_ref(v_localInstances_345_);
lean_inc_ref(v_lctx_344_);
lean_inc(v_zetaDeltaSet_343_);
v___x_353_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_zetaDeltaSet_343_);
lean_ctor_set(v___x_353_, 2, v_lctx_344_);
lean_ctor_set(v___x_353_, 3, v_localInstances_345_);
lean_ctor_set(v___x_353_, 4, v_defEqCtx_x3f_346_);
lean_ctor_set(v___x_353_, 5, v_synthPendingDepth_347_);
lean_ctor_set(v___x_353_, 6, v_customCanUnfoldPredicate_x3f_348_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*7, v_trackZetaDelta_342_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*7 + 1, v_univApprox_349_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*7 + 2, v_inTypeClassResolution_350_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*7 + 3, v_cacheInferType_351_);
lean_inc(v_a_314_);
lean_inc_ref(v_a_313_);
lean_inc(v_a_312_);
v___x_354_ = lean_whnf(v_type_310_, v___x_353_, v_a_312_, v_a_313_, v_a_314_);
v___y_317_ = v___x_354_;
goto v___jp_316_;
}
else
{
lean_object* v___x_355_; 
lean_inc(v_a_314_);
lean_inc_ref(v_a_313_);
lean_inc(v_a_312_);
lean_inc_ref(v_a_311_);
v___x_355_ = lean_whnf(v_type_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
v___y_317_ = v___x_355_;
goto v___jp_316_;
}
v___jp_316_:
{
if (lean_obj_tag(v___y_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v_a_318_ = lean_ctor_get(v___y_317_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___y_317_);
if (v_isSharedCheck_328_ == 0)
{
v___x_320_ = v___y_317_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___y_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
lean_inc(v_a_318_);
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; uint8_t v___x_325_; 
lean_inc(v_a_318_);
v___x_324_ = l_Lean_Expr_eta(v_a_318_);
v___x_325_ = lean_expr_eqv(v___x_324_, v_a_318_);
lean_dec(v_a_318_);
if (v___x_325_ == 0)
{
lean_dec_ref(v___x_323_);
v_type_310_ = v___x_324_;
goto _start;
}
else
{
lean_dec_ref(v___x_324_);
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
v_a_329_ = lean_ctor_get(v___y_317_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___y_317_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___y_317_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___y_317_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___boxed(lean_object* v_type_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(lean_object* v_msgData_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; lean_object* v_env_370_; uint8_t v___x_371_; lean_object* v_env_372_; lean_object* v___x_373_; lean_object* v_toCold_374_; lean_object* v_mctx_375_; lean_object* v_lctx_376_; lean_object* v_options_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_369_ = lean_st_ref_get(v___y_367_);
v_env_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc_ref(v_env_370_);
lean_dec(v___x_369_);
v___x_371_ = 0;
v_env_372_ = l_Lean_Environment_setRecordingDeps(v_env_370_, v___x_371_);
v___x_373_ = lean_st_ref_get(v___y_365_);
v_toCold_374_ = lean_ctor_get(v___y_366_, 0);
v_mctx_375_ = lean_ctor_get(v___x_373_, 0);
lean_inc_ref(v_mctx_375_);
lean_dec(v___x_373_);
v_lctx_376_ = lean_ctor_get(v___y_364_, 2);
v_options_377_ = lean_ctor_get(v_toCold_374_, 2);
lean_inc_ref(v_options_377_);
lean_inc_ref(v_lctx_376_);
v___x_378_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_378_, 0, v_env_372_);
lean_ctor_set(v___x_378_, 1, v_mctx_375_);
lean_ctor_set(v___x_378_, 2, v_lctx_376_);
lean_ctor_set(v___x_378_, 3, v_options_377_);
v___x_379_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v_msgData_363_);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6___boxed(lean_object* v_msgData_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msgData_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_ref_394_; lean_object* v___x_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_ref_394_ = lean_ctor_get(v___y_391_, 2);
v___x_395_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msg_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
lean_inc(v_ref_394_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_ref_394_);
lean_ctor_set(v___x_400_, 1, v_a_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 1);
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg___boxed(lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(lean_object* v_ref_412_, lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_toCold_419_; lean_object* v_currRecDepth_420_; lean_object* v_ref_421_; uint16_t v_optionFlags_422_; uint8_t v_suppressElabErrors_423_; uint8_t v_checkDeprecated_424_; uint8_t v_isRecordingDeps_425_; lean_object* v_ref_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_toCold_419_ = lean_ctor_get(v___y_416_, 0);
v_currRecDepth_420_ = lean_ctor_get(v___y_416_, 1);
v_ref_421_ = lean_ctor_get(v___y_416_, 2);
v_optionFlags_422_ = lean_ctor_get_uint16(v___y_416_, sizeof(void*)*3);
v_suppressElabErrors_423_ = lean_ctor_get_uint8(v___y_416_, sizeof(void*)*3 + 2);
v_checkDeprecated_424_ = lean_ctor_get_uint8(v___y_416_, sizeof(void*)*3 + 3);
v_isRecordingDeps_425_ = lean_ctor_get_uint8(v___y_416_, sizeof(void*)*3 + 4);
v_ref_426_ = l_Lean_replaceRef(v_ref_412_, v_ref_421_);
lean_inc(v_currRecDepth_420_);
lean_inc_ref(v_toCold_419_);
v___x_427_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_427_, 0, v_toCold_419_);
lean_ctor_set(v___x_427_, 1, v_currRecDepth_420_);
lean_ctor_set(v___x_427_, 2, v_ref_426_);
lean_ctor_set_uint16(v___x_427_, sizeof(void*)*3, v_optionFlags_422_);
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*3 + 2, v_suppressElabErrors_423_);
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*3 + 3, v_checkDeprecated_424_);
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*3 + 4, v_isRecordingDeps_425_);
v___x_428_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_413_, v___y_414_, v___y_415_, v___x_427_, v___y_417_);
lean_dec_ref_known(v___x_427_, 3);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg___boxed(lean_object* v_ref_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_429_, v_msg_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v_ref_429_);
return v_res_436_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_437_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_441_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
lean_ctor_set(v___x_443_, 3, v___x_442_);
lean_ctor_set(v___x_443_, 4, v___x_441_);
lean_ctor_set(v___x_443_, 5, v___x_441_);
lean_ctor_set(v___x_443_, 6, v___x_441_);
lean_ctor_set(v___x_443_, 7, v___x_441_);
lean_ctor_set(v___x_443_, 8, v___x_441_);
lean_ctor_set(v___x_443_, 9, v___x_441_);
lean_ctor_set(v___x_443_, 10, v___x_441_);
lean_ctor_set(v___x_443_, 11, v___x_440_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_unsigned_to_nat(32u);
v___x_445_ = lean_mk_empty_array_with_capacity(v___x_444_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_447_ = ((size_t)5ULL);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_unsigned_to_nat(32u);
v___x_450_ = lean_mk_empty_array_with_capacity(v___x_449_);
v___x_451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_452_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v___x_450_);
lean_ctor_set(v___x_452_, 2, v___x_448_);
lean_ctor_set(v___x_452_, 3, v___x_448_);
lean_ctor_set_usize(v___x_452_, 4, v___x_447_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = lean_box(1);
v___x_454_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_454_);
lean_ctor_set(v___x_456_, 2, v___x_453_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_478_, lean_object* v_declHint_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_env_484_; uint8_t v___x_485_; 
v___x_482_ = lean_box(0);
v___x_483_ = lean_st_ref_get(v___y_480_);
v_env_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_env_484_);
lean_dec(v___x_483_);
v___x_485_ = l_Lean_Name_isAnonymous(v_declHint_479_);
if (v___x_485_ == 0)
{
uint8_t v_isExporting_486_; 
v_isExporting_486_ = lean_ctor_get_uint8(v_env_484_, sizeof(void*)*13);
if (v_isExporting_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_479_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_msg_478_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; uint8_t v___x_489_; 
lean_inc_ref(v_env_484_);
v___x_488_ = l_Lean_Environment_setExporting(v_env_484_, v___x_485_);
lean_inc(v_declHint_479_);
lean_inc_ref(v___x_488_);
v___x_489_ = l_Lean_Environment_contains(v___x_488_, v_declHint_479_, v_isExporting_486_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_dec_ref(v___x_488_);
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_479_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_msg_478_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_c_496_; lean_object* v___x_497_; 
v___x_491_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_492_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_493_ = l_Lean_Options_empty;
lean_inc_ref(v___x_488_);
v___x_494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_494_, 0, v___x_488_);
lean_ctor_set(v___x_494_, 1, v___x_491_);
lean_ctor_set(v___x_494_, 2, v___x_492_);
lean_ctor_set(v___x_494_, 3, v___x_493_);
lean_inc(v_declHint_479_);
v___x_495_ = l_Lean_MessageData_ofConstName(v_declHint_479_, v___x_485_);
v_c_496_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_496_, 0, v___x_494_);
lean_ctor_set(v_c_496_, 1, v___x_495_);
v___x_497_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_488_, v_declHint_479_);
lean_dec_ref(v___x_488_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_479_);
v___x_498_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_c_496_);
v___x_500_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_MessageData_note(v___x_501_);
v___x_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_503_, 0, v_msg_478_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_539_; 
v_val_505_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_539_ == 0)
{
v___x_507_ = v___x_497_;
v_isShared_508_ = v_isSharedCheck_539_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_val_505_);
lean_dec(v___x_497_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_539_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v_moduleNames_510_; lean_object* v_mod_511_; uint8_t v___x_512_; 
v___x_509_ = l_Lean_Environment_header(v_env_484_);
lean_dec_ref(v_env_484_);
v_moduleNames_510_ = lean_ctor_get(v___x_509_, 4);
lean_inc_ref(v_moduleNames_510_);
lean_dec_ref(v___x_509_);
v_mod_511_ = lean_array_get(v___x_482_, v_moduleNames_510_, v_val_505_);
lean_dec(v_val_505_);
lean_dec_ref(v_moduleNames_510_);
v___x_512_ = l_Lean_isPrivateName(v_declHint_479_);
lean_dec(v_declHint_479_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_513_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v_c_496_);
v___x_515_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_MessageData_ofName(v_mod_511_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_MessageData_note(v___x_520_);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v_msg_478_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
lean_ctor_set(v___x_507_, 0, v___x_522_);
v___x_524_ = v___x_507_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_526_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_c_496_);
v___x_528_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_MessageData_ofName(v_mod_511_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = l_Lean_MessageData_note(v___x_533_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v_msg_478_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
lean_ctor_set(v___x_507_, 0, v___x_535_);
v___x_537_ = v___x_507_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_540_; 
lean_dec_ref(v_env_484_);
lean_dec(v_declHint_479_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_msg_478_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_541_, lean_object* v_declHint_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_541_, v_declHint_542_, v___y_543_);
lean_dec(v___y_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(lean_object* v_msg_546_, lean_object* v_declHint_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_563_; 
v___x_553_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_546_, v_declHint_547_, v___y_551_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = l_Lean_unknownIdentifierMessageTag;
v___x_559_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v_a_554_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_559_);
v___x_561_ = v___x_556_;
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
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9___boxed(lean_object* v_msg_564_, lean_object* v_declHint_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_564_, v_declHint_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(lean_object* v_ref_572_, lean_object* v_msg_573_, lean_object* v_declHint_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; lean_object* v_a_581_; lean_object* v___x_582_; 
v___x_580_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_573_, v_declHint_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___x_580_);
v___x_582_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_572_, v_a_581_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_ref_583_, lean_object* v_msg_584_, lean_object* v_declHint_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_583_, v_msg_584_, v_declHint_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v_ref_583_);
return v_res_591_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0));
v___x_594_ = l_Lean_stringToMessageData(v___x_593_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2));
v___x_597_ = l_Lean_stringToMessageData(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(lean_object* v_ref_598_, lean_object* v_constName_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_605_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1);
v___x_606_ = 0;
lean_inc(v_constName_599_);
v___x_607_ = l_Lean_MessageData_ofConstName(v_constName_599_, v___x_606_);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_598_, v___x_610_, v_constName_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___boxed(lean_object* v_ref_612_, lean_object* v_constName_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_612_, v_constName_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v_ref_612_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(lean_object* v_constName_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_ref_626_; lean_object* v___x_627_; 
v_ref_626_ = lean_ctor_get(v___y_623_, 2);
v___x_627_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_626_, v_constName_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg___boxed(lean_object* v_constName_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(lean_object* v_constName_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___x_641_; lean_object* v_env_642_; uint8_t v___x_643_; lean_object* v___x_644_; 
v___x_641_ = lean_st_ref_get(v___y_639_);
v_env_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc_ref(v_env_642_);
lean_dec(v___x_641_);
v___x_643_ = 0;
lean_inc(v_constName_635_);
v___x_644_ = l_Lean_Environment_find_x3f(v_env_642_, v_constName_635_, v___x_643_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
return v___x_645_;
}
else
{
lean_object* v_val_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_constName_635_);
v_val_646_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_val_646_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set_tag(v___x_648_, 0);
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_val_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4___boxed(lean_object* v_constName_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_constName_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(lean_object* v_binderType_661_, lean_object* v_body_662_, lean_object* v_binderName_663_, uint8_t v_binderInfo_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_binderType_661_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = lean_expr_instantiate1(v_body_662_, v_x_665_);
v___x_674_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_673_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; uint8_t v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v___x_676_ = l_Lean_Expr_isErased(v_a_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_688_; 
lean_inc(v_a_675_);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v___x_674_, 0);
lean_dec(v_unused_689_);
v___x_678_ = v___x_674_;
v_isShared_679_ = v_isSharedCheck_688_;
goto v_resetjp_677_;
}
else
{
lean_dec(v___x_674_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_688_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_mk_empty_array_with_capacity(v___x_680_);
v___x_682_ = lean_array_push(v___x_681_, v_x_665_);
v___x_683_ = lean_expr_abstract(v_a_675_, v___x_682_);
lean_dec_ref(v___x_682_);
lean_dec(v_a_675_);
v___x_684_ = l_Lean_Expr_lam___override(v_binderName_663_, v_a_672_, v___x_683_, v_binderInfo_664_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_684_);
v___x_686_ = v___x_678_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_dec(v_a_672_);
lean_dec_ref(v_x_665_);
lean_dec(v_binderName_663_);
return v___x_674_;
}
}
else
{
lean_dec(v_a_672_);
lean_dec_ref(v_x_665_);
lean_dec(v_binderName_663_);
return v___x_674_;
}
}
else
{
lean_dec_ref(v_x_665_);
lean_dec(v_binderName_663_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed(lean_object* v_binderType_690_, lean_object* v_body_691_, lean_object* v_binderName_692_, lean_object* v_binderInfo_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
uint8_t v_binderInfo_8918__boxed_700_; lean_object* v_res_701_; 
v_binderInfo_8918__boxed_700_ = lean_unbox(v_binderInfo_693_);
v_res_701_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(v_binderType_690_, v_body_691_, v_binderName_692_, v_binderInfo_8918__boxed_700_, v_x_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec_ref(v_body_691_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(lean_object* v_xs_702_, lean_object* v_body_703_, lean_object* v_binderName_704_, uint8_t v_binderInfo_705_, lean_object* v_d_706_, lean_object* v_x_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_d_714_; uint8_t v_isBorrowed_726_; lean_object* v___x_727_; 
v_isBorrowed_726_ = l_Lean_isMarkedBorrowed(v_d_706_);
v___x_727_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_d_706_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = lean_expr_abstract(v_a_728_, v_xs_702_);
lean_dec(v_a_728_);
if (v_isBorrowed_726_ == 0)
{
v_d_714_ = v___x_729_;
goto v___jp_713_;
}
else
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_markBorrowed(v___x_729_);
v_d_714_ = v___x_730_;
goto v___jp_713_;
}
}
else
{
lean_dec_ref(v_x_707_);
lean_dec(v_binderName_704_);
lean_dec_ref(v_body_703_);
lean_dec_ref(v_xs_702_);
return v___x_727_;
}
v___jp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_array_push(v_xs_702_, v_x_707_);
v___x_716_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_body_703_, v___x_715_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_725_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_725_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = l_Lean_Expr_forallE___override(v_binderName_704_, v_d_714_, v_a_717_, v_binderInfo_705_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_721_);
v___x_723_ = v___x_719_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_dec_ref(v_d_714_);
lean_dec(v_binderName_704_);
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed(lean_object* v_xs_731_, lean_object* v_body_732_, lean_object* v_binderName_733_, lean_object* v_binderInfo_734_, lean_object* v_d_735_, lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
uint8_t v_binderInfo_8940__boxed_742_; lean_object* v_res_743_; 
v_binderInfo_8940__boxed_742_ = lean_unbox(v_binderInfo_734_);
v_res_743_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(v_xs_731_, v_body_732_, v_binderName_733_, v_binderInfo_8940__boxed_742_, v_d_735_, v_x_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(lean_object* v_e_744_, lean_object* v_xs_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
if (lean_obj_tag(v_e_744_) == 7)
{
lean_object* v_binderName_751_; lean_object* v_binderType_752_; lean_object* v_body_753_; uint8_t v_binderInfo_754_; lean_object* v_d_755_; lean_object* v___x_756_; lean_object* v___f_757_; uint8_t v___x_758_; lean_object* v___x_759_; 
v_binderName_751_ = lean_ctor_get(v_e_744_, 0);
lean_inc_n(v_binderName_751_, 2);
v_binderType_752_ = lean_ctor_get(v_e_744_, 1);
lean_inc_ref(v_binderType_752_);
v_body_753_ = lean_ctor_get(v_e_744_, 2);
lean_inc_ref(v_body_753_);
v_binderInfo_754_ = lean_ctor_get_uint8(v_e_744_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_744_, 3);
v_d_755_ = lean_expr_instantiate_rev(v_binderType_752_, v_xs_745_);
lean_dec_ref(v_binderType_752_);
v___x_756_ = lean_box(v_binderInfo_754_);
lean_inc_ref(v_d_755_);
v___f_757_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed), 11, 5);
lean_closure_set(v___f_757_, 0, v_xs_745_);
lean_closure_set(v___f_757_, 1, v_body_753_);
lean_closure_set(v___f_757_, 2, v_binderName_751_);
lean_closure_set(v___f_757_, 3, v___x_756_);
lean_closure_set(v___f_757_, 4, v_d_755_);
v___x_758_ = 0;
v___x_759_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_751_, v_binderInfo_754_, v_d_755_, v___f_757_, v___x_758_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_expr_instantiate_rev(v_e_744_, v_xs_745_);
lean_dec_ref(v_e_744_);
v___x_761_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_760_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_770_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_770_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_expr_abstract(v_a_762_, v_xs_745_);
lean_dec_ref(v_xs_745_);
lean_dec(v_a_762_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
else
{
lean_dec_ref(v_xs_745_);
return v___x_761_;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0(void){
_start:
{
lean_object* v___x_771_; lean_object* v_dummy_772_; 
v___x_771_ = lean_box(0);
v_dummy_772_ = l_Lean_Expr_sort___override(v___x_771_);
return v_dummy_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(lean_object* v_type_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_785_; 
lean_inc_ref(v_type_776_);
v___x_785_ = l_Lean_Meta_isProp(v_type_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_847_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_847_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_847_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_847_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
uint8_t v___x_790_; 
v___x_790_ = lean_unbox(v_a_786_);
lean_dec(v_a_786_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_del_object(v___x_788_);
v___x_791_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
switch(lean_obj_tag(v_a_792_))
{
case 3:
{
return v___x_791_;
}
case 4:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
lean_inc_ref(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_794_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_792_, v___x_793_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_794_;
}
case 6:
{
lean_object* v_binderName_795_; lean_object* v_binderType_796_; lean_object* v_body_797_; uint8_t v_binderInfo_798_; lean_object* v___x_799_; lean_object* v___f_800_; uint8_t v___x_801_; lean_object* v___x_802_; 
lean_inc_ref(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v_binderName_795_ = lean_ctor_get(v_a_792_, 0);
lean_inc_n(v_binderName_795_, 2);
v_binderType_796_ = lean_ctor_get(v_a_792_, 1);
lean_inc_ref_n(v_binderType_796_, 2);
v_body_797_ = lean_ctor_get(v_a_792_, 2);
lean_inc_ref(v_body_797_);
v_binderInfo_798_ = lean_ctor_get_uint8(v_a_792_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_792_, 3);
v___x_799_ = lean_box(v_binderInfo_798_);
v___f_800_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_800_, 0, v_binderType_796_);
lean_closure_set(v___f_800_, 1, v_body_797_);
lean_closure_set(v___f_800_, 2, v_binderName_795_);
lean_closure_set(v___f_800_, 3, v___x_799_);
v___x_801_ = 0;
v___x_802_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_795_, v_binderInfo_798_, v_binderType_796_, v___f_800_, v___x_801_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_802_;
}
case 7:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_inc_ref(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_803_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_804_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_a_792_, v___x_803_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_804_;
}
case 5:
{
lean_object* v_dummy_805_; lean_object* v_nargs_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc_ref(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v_dummy_805_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0);
v_nargs_806_ = l_Lean_Expr_getAppNumArgs(v_a_792_);
lean_inc(v_nargs_806_);
v___x_807_ = lean_mk_array(v_nargs_806_, v_dummy_805_);
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_nat_sub(v_nargs_806_, v___x_808_);
lean_dec(v_nargs_806_);
v___x_810_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_a_792_, v___x_807_, v___x_809_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_810_;
}
case 1:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_inc_ref(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_811_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_812_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_792_, v___x_811_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_812_;
}
case 11:
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_841_; 
lean_inc_ref(v_a_792_);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_791_, 0);
lean_dec(v_unused_842_);
v___x_814_ = v___x_791_;
v_isShared_815_ = v_isSharedCheck_841_;
goto v_resetjp_813_;
}
else
{
lean_dec(v___x_791_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_841_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_typeName_816_; 
v_typeName_816_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_typeName_816_);
if (lean_obj_tag(v_typeName_816_) == 1)
{
lean_object* v_pre_817_; 
v_pre_817_ = lean_ctor_get(v_typeName_816_, 0);
if (lean_obj_tag(v_pre_817_) == 0)
{
lean_object* v_idx_818_; lean_object* v_struct_819_; lean_object* v_str_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_idx_818_ = lean_ctor_get(v_a_792_, 1);
lean_inc(v_idx_818_);
v_struct_819_ = lean_ctor_get(v_a_792_, 2);
lean_inc_ref(v_struct_819_);
lean_dec_ref_known(v_a_792_, 3);
v_str_820_ = lean_ctor_get(v_typeName_816_, 1);
lean_inc_ref(v_str_820_);
lean_dec_ref_known(v_typeName_816_, 2);
v___x_821_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1));
v___x_822_ = lean_string_dec_eq(v_str_820_, v___x_821_);
lean_dec_ref(v_str_820_);
if (v___x_822_ == 0)
{
lean_dec_ref(v_struct_819_);
lean_dec(v_idx_818_);
lean_del_object(v___x_814_);
goto v___jp_782_;
}
else
{
lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_nat_dec_eq(v_idx_818_, v___x_823_);
lean_dec(v_idx_818_);
if (v___x_824_ == 0)
{
lean_dec_ref(v_struct_819_);
lean_del_object(v___x_814_);
goto v___jp_782_;
}
else
{
if (lean_obj_tag(v_struct_819_) == 5)
{
lean_object* v_fn_825_; 
v_fn_825_ = lean_ctor_get(v_struct_819_, 0);
lean_inc_ref(v_fn_825_);
lean_dec_ref_known(v_struct_819_, 2);
if (lean_obj_tag(v_fn_825_) == 4)
{
lean_object* v_declName_826_; 
v_declName_826_ = lean_ctor_get(v_fn_825_, 0);
lean_inc(v_declName_826_);
if (lean_obj_tag(v_declName_826_) == 1)
{
lean_object* v_pre_827_; 
v_pre_827_ = lean_ctor_get(v_declName_826_, 0);
lean_inc(v_pre_827_);
if (lean_obj_tag(v_pre_827_) == 1)
{
lean_object* v_pre_828_; 
v_pre_828_ = lean_ctor_get(v_pre_827_, 0);
if (lean_obj_tag(v_pre_828_) == 0)
{
lean_object* v_us_829_; lean_object* v_str_830_; lean_object* v_str_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_us_829_ = lean_ctor_get(v_fn_825_, 1);
lean_inc(v_us_829_);
lean_dec_ref_known(v_fn_825_, 2);
v_str_830_ = lean_ctor_get(v_declName_826_, 1);
lean_inc_ref(v_str_830_);
lean_dec_ref_known(v_declName_826_, 2);
v_str_831_ = lean_ctor_get(v_pre_827_, 1);
lean_inc_ref(v_str_831_);
lean_dec_ref_known(v_pre_827_, 2);
v___x_832_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2));
v___x_833_ = lean_string_dec_eq(v_str_831_, v___x_832_);
lean_dec_ref(v_str_831_);
if (v___x_833_ == 0)
{
lean_dec_ref(v_str_830_);
lean_dec(v_us_829_);
lean_del_object(v___x_814_);
goto v___jp_782_;
}
else
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3));
v___x_835_ = lean_string_dec_eq(v_str_830_, v___x_834_);
lean_dec_ref(v_str_830_);
if (v___x_835_ == 0)
{
lean_dec(v_us_829_);
lean_del_object(v___x_814_);
goto v___jp_782_;
}
else
{
if (lean_obj_tag(v_us_829_) == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_836_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_837_ = l_Lean_mkConst(v___x_836_, v_us_829_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_837_);
v___x_839_ = v___x_814_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
lean_dec(v_us_829_);
lean_del_object(v___x_814_);
goto v___jp_782_;
}
}
}
}
else
{
lean_dec_ref_known(v_pre_827_, 2);
lean_dec_ref_known(v_declName_826_, 2);
lean_dec_ref_known(v_fn_825_, 2);
lean_del_object(v___x_814_);
goto v___jp_782_;
}
}
else
{
lean_dec_ref_known(v_declName_826_, 2);
lean_dec(v_pre_827_);
lean_dec_ref_known(v_fn_825_, 2);
lean_del_object(v___x_814_);
goto v___jp_782_;
}
}
else
{
lean_dec(v_declName_826_);
lean_dec_ref_known(v_fn_825_, 2);
lean_del_object(v___x_814_);
goto v___jp_782_;
}
}
else
{
lean_dec_ref(v_fn_825_);
lean_del_object(v___x_814_);
goto v___jp_782_;
}
}
else
{
lean_dec_ref(v_struct_819_);
lean_del_object(v___x_814_);
goto v___jp_782_;
}
}
}
}
else
{
lean_dec_ref_known(v_typeName_816_, 2);
lean_del_object(v___x_814_);
lean_dec_ref_known(v_a_792_, 3);
goto v___jp_782_;
}
}
else
{
lean_dec(v_typeName_816_);
lean_del_object(v___x_814_);
lean_dec_ref_known(v_a_792_, 3);
goto v___jp_782_;
}
}
}
default: 
{
lean_dec_ref_known(v___x_791_, 1);
goto v___jp_782_;
}
}
}
else
{
return v___x_791_;
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_845_; 
lean_dec_ref(v_type_776_);
v___x_843_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_843_);
v___x_845_ = v___x_788_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_type_776_);
v_a_848_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_785_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_785_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
v___jp_782_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(lean_object* v_as_856_, size_t v_sz_857_, size_t v_i_858_, lean_object* v_b_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_a_866_; uint8_t v___x_873_; 
v___x_873_ = lean_usize_dec_lt(v_i_858_, v_sz_857_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_b_859_);
return v___x_874_;
}
else
{
lean_object* v_a_875_; lean_object* v___x_876_; 
v_a_875_ = lean_array_uget_borrowed(v_as_856_, v_i_858_);
lean_inc(v_a_875_);
v___x_876_ = l_Lean_Meta_isProp(v_a_875_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; uint8_t v___x_878_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = lean_unbox(v_a_877_);
lean_dec(v_a_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
lean_inc(v_a_875_);
v___x_879_ = l_Lean_Compiler_LCNF_isPropFormer(v_a_875_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; uint8_t v___x_881_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_879_, 1);
v___x_881_ = lean_unbox(v_a_880_);
lean_dec(v_a_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
lean_inc(v_a_875_);
v___x_882_ = l_Lean_Meta_isTypeFormer(v_a_875_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; uint8_t v___x_884_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = lean_unbox(v_a_883_);
lean_dec(v_a_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_886_ = l_Lean_Expr_app___override(v_b_859_, v___x_885_);
v_a_866_ = v___x_886_;
goto v___jp_865_;
}
else
{
lean_object* v___x_887_; 
lean_inc(v_a_875_);
v___x_887_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_a_875_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_889_ = l_Lean_Expr_app___override(v_b_859_, v_a_888_);
v_a_866_ = v___x_889_;
goto v___jp_865_;
}
else
{
lean_dec_ref(v_b_859_);
return v___x_887_;
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_b_859_);
v_a_890_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_882_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_882_);
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
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
goto v___jp_870_;
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref(v_b_859_);
v_a_898_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_879_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_879_);
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
else
{
goto v___jp_870_;
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec_ref(v_b_859_);
v_a_906_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_876_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_876_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
v___jp_865_:
{
size_t v___x_867_; size_t v___x_868_; 
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_add(v_i_858_, v___x_867_);
v_i_858_ = v___x_868_;
v_b_859_ = v_a_866_;
goto _start;
}
v___jp_870_:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_872_ = l_Lean_Expr_app___override(v_b_859_, v___x_871_);
v_a_866_ = v___x_872_;
goto v___jp_865_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0));
v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(lean_object* v_f_917_, lean_object* v_args_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_fNew_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; 
switch(lean_obj_tag(v_f_917_))
{
case 4:
{
lean_object* v_declName_933_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___x_957_; lean_object* v_env_958_; uint8_t v_isExporting_959_; 
v_declName_933_ = lean_ctor_get(v_f_917_, 0);
v___x_957_ = lean_st_ref_get(v_a_922_);
v_env_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_ref(v_env_958_);
lean_dec(v___x_957_);
v_isExporting_959_ = lean_ctor_get_uint8(v_env_958_, sizeof(void*)*13);
lean_dec_ref(v_env_958_);
if (v_isExporting_959_ == 0)
{
v___y_935_ = v_a_919_;
v___y_936_ = v_a_920_;
v___y_937_ = v_a_921_;
v___y_938_ = v_a_922_;
goto v___jp_934_;
}
else
{
uint8_t v___x_960_; 
v___x_960_ = l_Lean_isPrivateName(v_declName_933_);
if (v___x_960_ == 0)
{
v___y_935_ = v_a_919_;
v___y_936_ = v_a_920_;
v___y_937_ = v_a_921_;
v___y_938_ = v_a_922_;
goto v___jp_934_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1);
v___x_962_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_961_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_dec_ref_known(v___x_962_, 1);
v___y_935_ = v_a_919_;
v___y_936_ = v_a_920_;
v___y_937_ = v_a_921_;
v___y_938_ = v_a_922_;
goto v___jp_934_;
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec_ref_known(v_f_917_, 2);
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
v___jp_934_:
{
lean_object* v___x_939_; 
lean_inc(v_declName_933_);
v___x_939_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_declName_933_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_948_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
if (lean_obj_tag(v_a_940_) == 5)
{
lean_dec_ref_known(v_a_940_, 1);
lean_del_object(v___x_942_);
v_fNew_925_ = v_f_917_;
v___y_926_ = v___y_935_;
v___y_927_ = v___y_936_;
v___y_928_ = v___y_937_;
v___y_929_ = v___y_938_;
goto v___jp_924_;
}
else
{
lean_object* v___x_944_; lean_object* v___x_946_; 
lean_dec(v_a_940_);
lean_dec_ref_known(v_f_917_, 2);
v___x_944_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref_known(v_f_917_, 2);
v_a_949_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_939_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_939_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
case 1:
{
v_fNew_925_ = v_f_917_;
v___y_926_ = v_a_919_;
v___y_927_ = v_a_920_;
v___y_928_ = v_a_921_;
v___y_929_ = v_a_922_;
goto v___jp_924_;
}
default: 
{
lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec_ref(v_f_917_);
v___x_971_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
v___jp_924_:
{
size_t v_sz_930_; size_t v___x_931_; lean_object* v___x_932_; 
v_sz_930_ = lean_array_size(v_args_918_);
v___x_931_ = ((size_t)0ULL);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_args_918_, v_sz_930_, v___x_931_, v_fNew_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
if (lean_obj_tag(v_x_973_) == 5)
{
lean_object* v_fn_981_; lean_object* v_arg_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_fn_981_ = lean_ctor_get(v_x_973_, 0);
lean_inc_ref(v_fn_981_);
v_arg_982_ = lean_ctor_get(v_x_973_, 1);
lean_inc_ref(v_arg_982_);
lean_dec_ref_known(v_x_973_, 2);
v___x_983_ = lean_array_set(v_x_974_, v_x_975_, v_arg_982_);
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = lean_nat_sub(v_x_975_, v___x_984_);
lean_dec(v_x_975_);
v_x_973_ = v_fn_981_;
v_x_974_ = v___x_983_;
v_x_975_ = v___x_985_;
goto _start;
}
else
{
lean_object* v___x_987_; 
lean_dec(v_x_975_);
v___x_987_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_x_973_, v_x_974_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec_ref(v_x_974_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0___boxed(lean_object* v_x_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_x_988_, v_x_989_, v_x_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___boxed(lean_object* v_e_997_, lean_object* v_xs_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_e_997_, v_xs_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___boxed(lean_object* v_f_1005_, lean_object* v_args_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_f_1005_, v_args_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec_ref(v_args_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3___boxed(lean_object* v_as_1013_, lean_object* v_sz_1014_, lean_object* v_i_1015_, lean_object* v_b_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
size_t v_sz_boxed_1022_; size_t v_i_boxed_1023_; lean_object* v_res_1024_; 
v_sz_boxed_1022_ = lean_unbox_usize(v_sz_1014_);
lean_dec(v_sz_1014_);
v_i_boxed_1023_ = lean_unbox_usize(v_i_1015_);
lean_dec(v_i_1015_);
v_res_1024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_as_1013_, v_sz_boxed_1022_, v_i_boxed_1023_, v_b_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_as_1013_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed(lean_object* v_type_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(lean_object* v_00_u03b1_1032_, lean_object* v_msg_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___boxed(lean_object* v_00_u03b1_1040_, lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(v_00_u03b1_1040_, v_msg_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(lean_object* v_00_u03b1_1048_, lean_object* v_constName_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___boxed(lean_object* v_00_u03b1_1056_, lean_object* v_constName_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(v_00_u03b1_1056_, v_constName_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(lean_object* v_00_u03b1_1064_, lean_object* v_ref_1065_, lean_object* v_constName_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_1065_, v_constName_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1073_, lean_object* v_ref_1074_, lean_object* v_constName_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(v_00_u03b1_1073_, v_ref_1074_, v_constName_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v_ref_1074_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(lean_object* v_00_u03b1_1082_, lean_object* v_ref_1083_, lean_object* v_msg_1084_, lean_object* v_declHint_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_1083_, v_msg_1084_, v_declHint_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_ref_1093_, lean_object* v_msg_1094_, lean_object* v_declHint_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(v_00_u03b1_1092_, v_ref_1093_, v_msg_1094_, v_declHint_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v_ref_1093_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(lean_object* v_msg_1102_, lean_object* v_declHint_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1102_, v_declHint_1103_, v___y_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_1110_, lean_object* v_declHint_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(v_msg_1110_, v_declHint_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(lean_object* v_00_u03b1_1118_, lean_object* v_ref_1119_, lean_object* v_msg_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1119_, v_msg_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_ref_1128_, lean_object* v_msg_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(v_00_u03b1_1127_, v_ref_1128_, v_msg_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v_ref_1128_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(lean_object* v_opts_1136_, lean_object* v_opt_1137_){
_start:
{
lean_object* v_name_1138_; lean_object* v_defValue_1139_; lean_object* v_map_1140_; lean_object* v___x_1141_; 
v_name_1138_ = lean_ctor_get(v_opt_1137_, 0);
v_defValue_1139_ = lean_ctor_get(v_opt_1137_, 1);
v_map_1140_ = lean_ctor_get(v_opts_1136_, 0);
v___x_1141_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1140_, v_name_1138_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_inc(v_defValue_1139_);
return v_defValue_1139_;
}
else
{
lean_object* v_val_1142_; 
v_val_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_val_1142_);
lean_dec_ref_known(v___x_1141_, 1);
if (lean_obj_tag(v_val_1142_) == 3)
{
lean_object* v_v_1143_; 
v_v_1143_ = lean_ctor_get(v_val_1142_, 0);
lean_inc(v_v_1143_);
lean_dec_ref_known(v_val_1142_, 1);
return v_v_1143_;
}
else
{
lean_dec(v_val_1142_);
lean_inc(v_defValue_1139_);
return v_defValue_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4___boxed(lean_object* v_opts_1144_, lean_object* v_opt_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v_opts_1144_, v_opt_1145_);
lean_dec_ref(v_opt_1145_);
lean_dec_ref(v_opts_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object* v_a_1147_, lean_object* v_diag_1148_, lean_object* v_a_x3f_1149_){
_start:
{
lean_object* v___x_1151_; lean_object* v_mctx_1152_; lean_object* v_cache_1153_; lean_object* v_zetaDeltaFVarIds_1154_; lean_object* v_postponed_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1165_; 
v___x_1151_ = lean_st_ref_take(v_a_1147_);
v_mctx_1152_ = lean_ctor_get(v___x_1151_, 0);
v_cache_1153_ = lean_ctor_get(v___x_1151_, 1);
v_zetaDeltaFVarIds_1154_ = lean_ctor_get(v___x_1151_, 2);
v_postponed_1155_ = lean_ctor_get(v___x_1151_, 3);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1151_, 4);
lean_dec(v_unused_1166_);
v___x_1157_ = v___x_1151_;
v_isShared_1158_ = v_isSharedCheck_1165_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_postponed_1155_);
lean_inc(v_zetaDeltaFVarIds_1154_);
lean_inc(v_cache_1153_);
lean_inc(v_mctx_1152_);
lean_dec(v___x_1151_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1165_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_box(0);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 4, v_diag_1148_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_mctx_1152_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_cache_1153_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_zetaDeltaFVarIds_1154_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_postponed_1155_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_diag_1148_);
v___x_1161_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_st_ref_put(v_a_1147_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1159_);
return v___x_1163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object* v_a_1167_, lean_object* v_diag_1168_, lean_object* v_a_x3f_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1167_, v_diag_1168_, v_a_x3f_1169_);
lean_dec(v_a_x3f_1169_);
lean_dec(v_a_1167_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14___redArg(lean_object* v_f_1172_, lean_object* v_keys_1173_, lean_object* v_vals_1174_, lean_object* v_i_1175_, lean_object* v_acc_1176_){
_start:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_array_get_size(v_keys_1173_);
v___x_1178_ = lean_nat_dec_lt(v_i_1175_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v_i_1175_);
lean_dec(v_f_1172_);
return v_acc_1176_;
}
else
{
lean_object* v_k_1179_; lean_object* v_v_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_k_1179_ = lean_array_fget_borrowed(v_keys_1173_, v_i_1175_);
v_v_1180_ = lean_array_fget_borrowed(v_vals_1174_, v_i_1175_);
lean_inc(v_f_1172_);
lean_inc(v_v_1180_);
lean_inc(v_k_1179_);
v___x_1181_ = lean_apply_3(v_f_1172_, v_acc_1176_, v_k_1179_, v_v_1180_);
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = lean_nat_add(v_i_1175_, v___x_1182_);
lean_dec(v_i_1175_);
v_i_1175_ = v___x_1183_;
v_acc_1176_ = v___x_1181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14___redArg___boxed(lean_object* v_f_1185_, lean_object* v_keys_1186_, lean_object* v_vals_1187_, lean_object* v_i_1188_, lean_object* v_acc_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14___redArg(v_f_1185_, v_keys_1186_, v_vals_1187_, v_i_1188_, v_acc_1189_);
lean_dec_ref(v_vals_1187_);
lean_dec_ref(v_keys_1186_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(lean_object* v_f_1191_, lean_object* v_as_1192_, size_t v_i_1193_, size_t v_stop_1194_, lean_object* v_b_1195_){
_start:
{
lean_object* v___y_1197_; uint8_t v___x_1201_; 
v___x_1201_ = lean_usize_dec_eq(v_i_1193_, v_stop_1194_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_array_uget_borrowed(v_as_1192_, v_i_1193_);
switch(lean_obj_tag(v___x_1202_))
{
case 0:
{
lean_object* v_key_1203_; lean_object* v_val_1204_; lean_object* v___x_1205_; 
v_key_1203_ = lean_ctor_get(v___x_1202_, 0);
v_val_1204_ = lean_ctor_get(v___x_1202_, 1);
lean_inc(v_f_1191_);
lean_inc(v_val_1204_);
lean_inc(v_key_1203_);
v___x_1205_ = lean_apply_3(v_f_1191_, v_b_1195_, v_key_1203_, v_val_1204_);
v___y_1197_ = v___x_1205_;
goto v___jp_1196_;
}
case 1:
{
lean_object* v_node_1206_; lean_object* v___x_1207_; 
v_node_1206_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_f_1191_);
v___x_1207_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___redArg(v_f_1191_, v_node_1206_, v_b_1195_);
v___y_1197_ = v___x_1207_;
goto v___jp_1196_;
}
default: 
{
v___y_1197_ = v_b_1195_;
goto v___jp_1196_;
}
}
}
else
{
lean_dec(v_f_1191_);
return v_b_1195_;
}
v___jp_1196_:
{
size_t v___x_1198_; size_t v___x_1199_; 
v___x_1198_ = ((size_t)1ULL);
v___x_1199_ = lean_usize_add(v_i_1193_, v___x_1198_);
v_i_1193_ = v___x_1199_;
v_b_1195_ = v___y_1197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_f_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
if (lean_obj_tag(v_x_1209_) == 0)
{
lean_object* v_es_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_es_1211_ = lean_ctor_get(v_x_1209_, 0);
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_array_get_size(v_es_1211_);
v___x_1214_ = lean_nat_dec_lt(v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_dec(v_f_1208_);
return v_x_1210_;
}
else
{
size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = ((size_t)0ULL);
v___x_1216_ = lean_usize_of_nat(v___x_1213_);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_f_1208_, v_es_1211_, v___x_1215_, v___x_1216_, v_x_1210_);
return v___x_1217_;
}
}
else
{
lean_object* v_ks_1218_; lean_object* v_vs_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_ks_1218_ = lean_ctor_get(v_x_1209_, 0);
v_vs_1219_ = lean_ctor_get(v_x_1209_, 1);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14___redArg(v_f_1208_, v_ks_1218_, v_vs_1219_, v___x_1220_, v_x_1210_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_f_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___redArg(v_f_1222_, v_x_1223_, v_x_1224_);
lean_dec_ref(v_x_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13___redArg___boxed(lean_object* v_f_1226_, lean_object* v_as_1227_, lean_object* v_i_1228_, lean_object* v_stop_1229_, lean_object* v_b_1230_){
_start:
{
size_t v_i_boxed_1231_; size_t v_stop_boxed_1232_; lean_object* v_res_1233_; 
v_i_boxed_1231_ = lean_unbox_usize(v_i_1228_);
lean_dec(v_i_1228_);
v_stop_boxed_1232_ = lean_unbox_usize(v_stop_1229_);
lean_dec(v_stop_1229_);
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_f_1226_, v_as_1227_, v_i_boxed_1231_, v_stop_boxed_1232_, v_b_1230_);
lean_dec_ref(v_as_1227_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___redArg___lam__0(lean_object* v_f_1234_, lean_object* v_x1_1235_, lean_object* v_x2_1236_, lean_object* v_x3_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_apply_3(v_f_1234_, v_x1_1235_, v_x2_1236_, v_x3_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___redArg(lean_object* v_map_1239_, lean_object* v_f_1240_, lean_object* v_init_1241_){
_start:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; 
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1242_, 0, v_f_1240_);
v___x_1243_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___redArg(v___f_1242_, v_map_1239_, v_init_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___redArg___boxed(lean_object* v_map_1244_, lean_object* v_f_1245_, lean_object* v_init_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___redArg(v_map_1244_, v_f_1245_, v_init_1246_);
lean_dec_ref(v_map_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0(lean_object* v_ps_1248_, lean_object* v_k_1249_, lean_object* v_v_1250_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_k_1249_);
lean_ctor_set(v___x_1251_, 1, v_v_1250_);
v___x_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v_ps_1248_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(lean_object* v_m_1254_){
_start:
{
lean_object* v___f_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___f_1255_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0));
v___x_1256_ = lean_box(0);
v___x_1257_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___redArg(v_m_1254_, v___f_1255_, v___x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___boxed(lean_object* v_m_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1258_);
lean_dec_ref(v_m_1258_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8(lean_object* v_o_1263_, lean_object* v_k_1264_, uint8_t v_v_1265_){
_start:
{
lean_object* v_map_1266_; uint8_t v_hasTrace_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1281_; 
v_map_1266_ = lean_ctor_get(v_o_1263_, 0);
v_hasTrace_1267_ = lean_ctor_get_uint8(v_o_1263_, sizeof(void*)*1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_o_1263_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1269_ = v_o_1263_;
v_isShared_1270_ = v_isSharedCheck_1281_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_map_1266_);
lean_dec(v_o_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1281_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1271_, 0, v_v_1265_);
lean_inc(v_k_1264_);
v___x_1272_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1264_, v___x_1271_, v_map_1266_);
if (v_hasTrace_1267_ == 0)
{
lean_object* v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1276_; 
v___x_1273_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8___closed__1));
v___x_1274_ = l_Lean_Name_isPrefixOf(v___x_1273_, v_k_1264_);
lean_dec(v_k_1264_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1272_);
v___x_1276_ = v___x_1269_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1272_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_ctor_set_uint8(v___x_1276_, sizeof(void*)*1, v___x_1274_);
return v___x_1276_;
}
}
else
{
lean_object* v___x_1279_; 
lean_dec(v_k_1264_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1272_);
v___x_1279_ = v___x_1269_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, sizeof(void*)*1, v_hasTrace_1267_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8___boxed(lean_object* v_o_1282_, lean_object* v_k_1283_, lean_object* v_v_1284_){
_start:
{
uint8_t v_v_boxed_1285_; lean_object* v_res_1286_; 
v_v_boxed_1285_ = lean_unbox(v_v_1284_);
v_res_1286_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8(v_o_1282_, v_k_1283_, v_v_boxed_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(lean_object* v_opts_1287_, lean_object* v_opt_1288_, uint8_t v_val_1289_){
_start:
{
lean_object* v_name_1290_; lean_object* v___x_1291_; 
v_name_1290_ = lean_ctor_get(v_opt_1288_, 0);
lean_inc(v_name_1290_);
lean_dec_ref(v_opt_1288_);
v___x_1291_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5_spec__8(v_opts_1287_, v_name_1290_, v_val_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5___boxed(lean_object* v_opts_1292_, lean_object* v_opt_1293_, lean_object* v_val_1294_){
_start:
{
uint8_t v_val_boxed_1295_; lean_object* v_res_1296_; 
v_val_boxed_1295_ = lean_unbox(v_val_1294_);
v_res_1296_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v_opts_1292_, v_opt_1293_, v_val_boxed_1295_);
return v_res_1296_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg___closed__0);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v___dummy_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg();
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(lean_object* v___y_1303_, uint8_t v_isExporting_1304_, lean_object* v___x_1305_, lean_object* v___y_1306_, lean_object* v___x_1307_, lean_object* v_a_x3f_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v_env_1311_; lean_object* v_nextMacroScope_1312_; lean_object* v_ngen_1313_; lean_object* v_auxDeclNGen_1314_; lean_object* v_traceState_1315_; lean_object* v_recordedDeps_1316_; lean_object* v_messages_1317_; lean_object* v_infoState_1318_; lean_object* v_snapshotTasks_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1344_; 
v___x_1310_ = lean_st_ref_take(v___y_1303_);
v_env_1311_ = lean_ctor_get(v___x_1310_, 0);
v_nextMacroScope_1312_ = lean_ctor_get(v___x_1310_, 1);
v_ngen_1313_ = lean_ctor_get(v___x_1310_, 2);
v_auxDeclNGen_1314_ = lean_ctor_get(v___x_1310_, 3);
v_traceState_1315_ = lean_ctor_get(v___x_1310_, 4);
v_recordedDeps_1316_ = lean_ctor_get(v___x_1310_, 6);
v_messages_1317_ = lean_ctor_get(v___x_1310_, 7);
v_infoState_1318_ = lean_ctor_get(v___x_1310_, 8);
v_snapshotTasks_1319_ = lean_ctor_get(v___x_1310_, 9);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v___x_1310_, 5);
lean_dec(v_unused_1345_);
v___x_1321_ = v___x_1310_;
v_isShared_1322_ = v_isSharedCheck_1344_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_snapshotTasks_1319_);
lean_inc(v_infoState_1318_);
lean_inc(v_messages_1317_);
lean_inc(v_recordedDeps_1316_);
lean_inc(v_traceState_1315_);
lean_inc(v_auxDeclNGen_1314_);
lean_inc(v_ngen_1313_);
lean_inc(v_nextMacroScope_1312_);
lean_inc(v_env_1311_);
lean_dec(v___x_1310_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1344_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = l_Lean_Environment_setExporting(v_env_1311_, v_isExporting_1304_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 5, v___x_1305_);
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_nextMacroScope_1312_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_ngen_1313_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_auxDeclNGen_1314_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_traceState_1315_);
lean_ctor_set(v_reuseFailAlloc_1343_, 5, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1343_, 6, v_recordedDeps_1316_);
lean_ctor_set(v_reuseFailAlloc_1343_, 7, v_messages_1317_);
lean_ctor_set(v_reuseFailAlloc_1343_, 8, v_infoState_1318_);
lean_ctor_set(v_reuseFailAlloc_1343_, 9, v_snapshotTasks_1319_);
v___x_1325_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_mctx_1328_; lean_object* v_zetaDeltaFVarIds_1329_; lean_object* v_postponed_1330_; lean_object* v_diag_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1341_; 
v___x_1326_ = lean_st_ref_put(v___y_1303_, v___x_1325_);
v___x_1327_ = lean_st_ref_take(v___y_1306_);
v_mctx_1328_ = lean_ctor_get(v___x_1327_, 0);
v_zetaDeltaFVarIds_1329_ = lean_ctor_get(v___x_1327_, 2);
v_postponed_1330_ = lean_ctor_get(v___x_1327_, 3);
v_diag_1331_ = lean_ctor_get(v___x_1327_, 4);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v___x_1327_, 1);
lean_dec(v_unused_1342_);
v___x_1333_ = v___x_1327_;
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_diag_1331_);
lean_inc(v_postponed_1330_);
lean_inc(v_zetaDeltaFVarIds_1329_);
lean_inc(v_mctx_1328_);
lean_dec(v___x_1327_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_box(0);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v___x_1307_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_mctx_1328_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_zetaDeltaFVarIds_1329_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_postponed_1330_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_diag_1331_);
v___x_1337_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_st_ref_put(v___y_1306_, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1335_);
return v___x_1339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0___boxed(lean_object* v___y_1346_, lean_object* v_isExporting_1347_, lean_object* v___x_1348_, lean_object* v___y_1349_, lean_object* v___x_1350_, lean_object* v_a_x3f_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v_isExporting_boxed_1353_; lean_object* v_res_1354_; 
v_isExporting_boxed_1353_ = lean_unbox(v_isExporting_1347_);
v_res_1354_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1346_, v_isExporting_boxed_1353_, v___x_1348_, v___y_1349_, v___x_1350_, v_a_x3f_1351_);
lean_dec(v_a_x3f_1351_);
lean_dec(v___y_1349_);
lean_dec(v___y_1346_);
return v_res_1354_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
return v___x_1358_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2___redArg();
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0);
v___x_1361_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
v___x_1362_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v___x_1360_);
lean_ctor_set(v___x_1362_, 2, v___x_1360_);
lean_ctor_set(v___x_1362_, 3, v___x_1360_);
lean_ctor_set(v___x_1362_, 4, v___x_1360_);
lean_ctor_set(v___x_1362_, 5, v___x_1360_);
lean_ctor_set(v___x_1362_, 6, v___x_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(lean_object* v_x_1363_, uint8_t v_isExporting_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v_env_1371_; lean_object* v___x_1372_; uint8_t v_isModule_1373_; 
v___x_1370_ = lean_st_ref_get(v___y_1368_);
v_env_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc_ref(v_env_1371_);
lean_dec(v___x_1370_);
v___x_1372_ = l_Lean_Environment_header(v_env_1371_);
v_isModule_1373_ = lean_ctor_get_uint8(v___x_1372_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1372_);
if (v_isModule_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_dec_ref(v_env_1371_);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
v___x_1374_ = lean_apply_5(v_x_1363_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, lean_box(0));
return v___x_1374_;
}
else
{
uint8_t v_isExporting_1375_; 
v_isExporting_1375_ = lean_ctor_get_uint8(v_env_1371_, sizeof(void*)*13);
lean_dec_ref(v_env_1371_);
if (v_isExporting_1364_ == 0)
{
if (v_isExporting_1375_ == 0)
{
lean_object* v___x_1442_; 
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
v___x_1442_ = lean_apply_5(v_x_1363_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, lean_box(0));
return v___x_1442_;
}
else
{
goto v___jp_1376_;
}
}
else
{
if (v_isExporting_1375_ == 0)
{
goto v___jp_1376_;
}
else
{
lean_object* v___x_1443_; 
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
v___x_1443_ = lean_apply_5(v_x_1363_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, lean_box(0));
return v___x_1443_;
}
}
v___jp_1376_:
{
lean_object* v___x_1377_; lean_object* v_env_1378_; lean_object* v_nextMacroScope_1379_; lean_object* v_ngen_1380_; lean_object* v_auxDeclNGen_1381_; lean_object* v_traceState_1382_; lean_object* v_recordedDeps_1383_; lean_object* v_messages_1384_; lean_object* v_infoState_1385_; lean_object* v_snapshotTasks_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1440_; 
v___x_1377_ = lean_st_ref_take(v___y_1368_);
v_env_1378_ = lean_ctor_get(v___x_1377_, 0);
v_nextMacroScope_1379_ = lean_ctor_get(v___x_1377_, 1);
v_ngen_1380_ = lean_ctor_get(v___x_1377_, 2);
v_auxDeclNGen_1381_ = lean_ctor_get(v___x_1377_, 3);
v_traceState_1382_ = lean_ctor_get(v___x_1377_, 4);
v_recordedDeps_1383_ = lean_ctor_get(v___x_1377_, 6);
v_messages_1384_ = lean_ctor_get(v___x_1377_, 7);
v_infoState_1385_ = lean_ctor_get(v___x_1377_, 8);
v_snapshotTasks_1386_ = lean_ctor_get(v___x_1377_, 9);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v___x_1377_, 5);
lean_dec(v_unused_1441_);
v___x_1388_ = v___x_1377_;
v_isShared_1389_ = v_isSharedCheck_1440_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_snapshotTasks_1386_);
lean_inc(v_infoState_1385_);
lean_inc(v_messages_1384_);
lean_inc(v_recordedDeps_1383_);
lean_inc(v_traceState_1382_);
lean_inc(v_auxDeclNGen_1381_);
lean_inc(v_ngen_1380_);
lean_inc(v_nextMacroScope_1379_);
lean_inc(v_env_1378_);
lean_dec(v___x_1377_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1440_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1390_ = l_Lean_Environment_setExporting(v_env_1378_, v_isExporting_1364_);
v___x_1391_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 5, v___x_1391_);
lean_ctor_set(v___x_1388_, 0, v___x_1390_);
v___x_1393_ = v___x_1388_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_nextMacroScope_1379_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_ngen_1380_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v_auxDeclNGen_1381_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v_traceState_1382_);
lean_ctor_set(v_reuseFailAlloc_1439_, 5, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1439_, 6, v_recordedDeps_1383_);
lean_ctor_set(v_reuseFailAlloc_1439_, 7, v_messages_1384_);
lean_ctor_set(v_reuseFailAlloc_1439_, 8, v_infoState_1385_);
lean_ctor_set(v_reuseFailAlloc_1439_, 9, v_snapshotTasks_1386_);
v___x_1393_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_mctx_1396_; lean_object* v_zetaDeltaFVarIds_1397_; lean_object* v_postponed_1398_; lean_object* v_diag_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1437_; 
v___x_1394_ = lean_st_ref_put(v___y_1368_, v___x_1393_);
v___x_1395_ = lean_st_ref_take(v___y_1366_);
v_mctx_1396_ = lean_ctor_get(v___x_1395_, 0);
v_zetaDeltaFVarIds_1397_ = lean_ctor_get(v___x_1395_, 2);
v_postponed_1398_ = lean_ctor_get(v___x_1395_, 3);
v_diag_1399_ = lean_ctor_get(v___x_1395_, 4);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v___x_1395_, 1);
lean_dec(v_unused_1438_);
v___x_1401_ = v___x_1395_;
v_isShared_1402_ = v_isSharedCheck_1437_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_diag_1399_);
lean_inc(v_postponed_1398_);
lean_inc(v_zetaDeltaFVarIds_1397_);
lean_inc(v_mctx_1396_);
lean_dec(v___x_1395_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1437_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v___x_1403_);
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_mctx_1396_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_zetaDeltaFVarIds_1397_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_postponed_1398_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v_diag_1399_);
v___x_1405_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; lean_object* v_r_1407_; 
v___x_1406_ = lean_st_ref_put(v___y_1366_, v___x_1405_);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
v_r_1407_ = lean_apply_5(v_x_1363_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, lean_box(0));
if (lean_obj_tag(v_r_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1424_; 
v_a_1408_ = lean_ctor_get(v_r_1407_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1410_ = v_r_1407_;
v_isShared_1411_ = v_isSharedCheck_1424_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v_r_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1424_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
lean_inc(v_a_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 1);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v___x_1414_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1368_, v_isExporting_1375_, v___x_1391_, v___y_1366_, v___x_1403_, v___x_1413_);
lean_dec_ref(v___x_1413_);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1414_, 0);
lean_dec(v_unused_1422_);
v___x_1416_ = v___x_1414_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v___x_1414_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v_a_1408_);
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1408_);
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
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
v_a_1425_ = lean_ctor_get(v_r_1407_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v_r_1407_, 1);
v___x_1426_ = lean_box(0);
v___x_1427_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1368_, v_isExporting_1375_, v___x_1391_, v___y_1366_, v___x_1403_, v___x_1426_);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v___x_1427_, 0);
lean_dec(v_unused_1435_);
v___x_1429_ = v___x_1427_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_dec(v___x_1427_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 1);
lean_ctor_set(v___x_1429_, 0, v_a_1425_);
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1425_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___boxed(lean_object* v_x_1444_, lean_object* v_isExporting_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
uint8_t v_isExporting_boxed_1451_; lean_object* v_res_1452_; 
v_isExporting_boxed_1451_ = lean_unbox(v_isExporting_1445_);
v_res_1452_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1444_, v_isExporting_boxed_1451_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_1453_, lean_object* v_vals_1454_, lean_object* v_i_1455_, lean_object* v_k_1456_){
_start:
{
lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = lean_array_get_size(v_keys_1453_);
v___x_1458_ = lean_nat_dec_lt(v_i_1455_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_dec(v_i_1455_);
v___x_1459_ = lean_box(0);
return v___x_1459_;
}
else
{
lean_object* v_k_x27_1460_; uint8_t v___x_1461_; 
v_k_x27_1460_ = lean_array_fget_borrowed(v_keys_1453_, v_i_1455_);
v___x_1461_ = lean_name_eq(v_k_1456_, v_k_x27_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_add(v_i_1455_, v___x_1462_);
lean_dec(v_i_1455_);
v_i_1455_ = v___x_1463_;
goto _start;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_array_fget_borrowed(v_vals_1454_, v_i_1455_);
lean_dec(v_i_1455_);
lean_inc(v___x_1465_);
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1467_, lean_object* v_vals_1468_, lean_object* v_i_1469_, lean_object* v_k_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5___redArg(v_keys_1467_, v_vals_1468_, v_i_1469_, v_k_1470_);
lean_dec(v_k_1470_);
lean_dec_ref(v_vals_1468_);
lean_dec_ref(v_keys_1467_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2___redArg(lean_object* v_x_1472_, size_t v_x_1473_, lean_object* v_x_1474_){
_start:
{
if (lean_obj_tag(v_x_1472_) == 0)
{
lean_object* v_es_1475_; lean_object* v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; lean_object* v_j_1479_; lean_object* v___x_1480_; 
v_es_1475_ = lean_ctor_get(v_x_1472_, 0);
v___x_1476_ = lean_box(2);
v___x_1477_ = ((size_t)31ULL);
v___x_1478_ = lean_usize_land(v_x_1473_, v___x_1477_);
v_j_1479_ = lean_usize_to_nat(v___x_1478_);
v___x_1480_ = lean_array_get_borrowed(v___x_1476_, v_es_1475_, v_j_1479_);
lean_dec(v_j_1479_);
switch(lean_obj_tag(v___x_1480_))
{
case 0:
{
lean_object* v_key_1481_; lean_object* v_val_1482_; uint8_t v___x_1483_; 
v_key_1481_ = lean_ctor_get(v___x_1480_, 0);
v_val_1482_ = lean_ctor_get(v___x_1480_, 1);
v___x_1483_ = lean_name_eq(v_x_1474_, v_key_1481_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_box(0);
return v___x_1484_;
}
else
{
lean_object* v___x_1485_; 
lean_inc(v_val_1482_);
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_val_1482_);
return v___x_1485_;
}
}
case 1:
{
lean_object* v_node_1486_; size_t v___x_1487_; size_t v___x_1488_; 
v_node_1486_ = lean_ctor_get(v___x_1480_, 0);
v___x_1487_ = ((size_t)5ULL);
v___x_1488_ = lean_usize_shift_right(v_x_1473_, v___x_1487_);
v_x_1472_ = v_node_1486_;
v_x_1473_ = v___x_1488_;
goto _start;
}
default: 
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_box(0);
return v___x_1490_;
}
}
}
else
{
lean_object* v_ks_1491_; lean_object* v_vs_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_ks_1491_ = lean_ctor_get(v_x_1472_, 0);
v_vs_1492_ = lean_ctor_get(v_x_1472_, 1);
v___x_1493_ = lean_unsigned_to_nat(0u);
v___x_1494_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5___redArg(v_ks_1491_, v_vs_1492_, v___x_1493_, v_x_1474_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2___redArg___boxed(lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
size_t v_x_17660__boxed_1498_; lean_object* v_res_1499_; 
v_x_17660__boxed_1498_ = lean_unbox_usize(v_x_1496_);
lean_dec(v_x_1496_);
v_res_1499_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2___redArg(v_x_1495_, v_x_17660__boxed_1498_, v_x_1497_);
lean_dec(v_x_1497_);
lean_dec_ref(v_x_1495_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
uint64_t v___y_1503_; 
if (lean_obj_tag(v_x_1501_) == 0)
{
uint64_t v___x_1506_; 
v___x_1506_ = 1723ULL;
v___y_1503_ = v___x_1506_;
goto v___jp_1502_;
}
else
{
uint64_t v_hash_1507_; 
v_hash_1507_ = lean_ctor_get_uint64(v_x_1501_, sizeof(void*)*2);
v___y_1503_ = v_hash_1507_;
goto v___jp_1502_;
}
v___jp_1502_:
{
size_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_uint64_to_usize(v___y_1503_);
v___x_1505_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2___redArg(v_x_1500_, v___x_1504_, v_x_1501_);
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___boxed(lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1508_, v_x_1509_);
lean_dec(v_x_1509_);
lean_dec_ref(v_x_1508_);
return v_res_1510_;
}
}
static lean_object* _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0));
v___x_1513_ = l_Lean_stringToMessageData(v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(lean_object* v___x_1514_, lean_object* v___x_1515_, uint8_t v___x_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
if (lean_obj_tag(v_a_1517_) == 0)
{
lean_object* v___x_1519_; 
lean_dec_ref(v___x_1515_);
v___x_1519_ = lean_array_to_list(v_a_1518_);
return v___x_1519_;
}
else
{
lean_object* v_head_1520_; lean_object* v_tail_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1564_; 
v_head_1520_ = lean_ctor_get(v_a_1517_, 0);
v_tail_1521_ = lean_ctor_get(v_a_1517_, 1);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_a_1517_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1523_ = v_a_1517_;
v_isShared_1524_ = v_isSharedCheck_1564_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_tail_1521_);
lean_inc(v_head_1520_);
lean_dec(v_a_1517_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1564_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_fst_1525_; lean_object* v_snd_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1563_; 
v_fst_1525_ = lean_ctor_get(v_head_1520_, 0);
v_snd_1526_ = lean_ctor_get(v_head_1520_, 1);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_head_1520_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1528_ = v_head_1520_;
v_isShared_1529_ = v_isSharedCheck_1563_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snd_1526_);
lean_inc(v_fst_1525_);
lean_dec(v_head_1520_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1563_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_unfoldAxiomCounter_1530_; lean_object* v___x_1531_; lean_object* v___y_1533_; lean_object* v___x_1561_; 
v_unfoldAxiomCounter_1530_ = lean_ctor_get(v___x_1514_, 1);
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1561_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_unfoldAxiomCounter_1530_, v_fst_1525_);
if (lean_obj_tag(v___x_1561_) == 0)
{
v___y_1533_ = v___x_1531_;
goto v___jp_1532_;
}
else
{
lean_object* v_val_1562_; 
v_val_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_val_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v___y_1533_ = v_val_1562_;
goto v___jp_1532_;
}
v___jp_1532_:
{
lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1534_ = lean_nat_sub(v_snd_1526_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec(v_snd_1526_);
v___x_1535_ = lean_nat_dec_lt(v___x_1531_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_dec(v___x_1534_);
lean_del_object(v___x_1528_);
lean_dec(v_fst_1525_);
lean_del_object(v___x_1523_);
v_a_1517_ = v_tail_1521_;
goto _start;
}
else
{
lean_object* v___x_1537_; 
lean_inc(v_fst_1525_);
lean_inc_ref(v___x_1515_);
v___x_1537_ = l_Lean_getOriginalConstKind_x3f(v___x_1515_, v_fst_1525_);
if (lean_obj_tag(v___x_1537_) == 1)
{
lean_object* v_val_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1559_; 
v_val_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1559_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_val_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1559_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_unbox(v_val_1538_);
lean_dec(v_val_1538_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1543_ = l_Lean_MessageData_ofConstName(v_fst_1525_, v___x_1516_);
v___x_1544_ = lean_obj_once(&l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1, &l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1_once, _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1);
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 7);
lean_ctor_set(v___x_1528_, 1, v___x_1544_);
lean_ctor_set(v___x_1528_, 0, v___x_1543_);
v___x_1546_ = v___x_1528_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = l_Nat_reprFast(v___x_1534_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 3);
lean_ctor_set(v___x_1540_, 0, v___x_1547_);
v___x_1549_ = v___x_1540_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = l_Lean_MessageData_ofFormat(v___x_1549_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set_tag(v___x_1523_, 7);
lean_ctor_set(v___x_1523_, 1, v___x_1550_);
lean_ctor_set(v___x_1523_, 0, v___x_1546_);
v___x_1552_ = v___x_1523_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_array_push(v_a_1518_, v___x_1552_);
v_a_1517_ = v_tail_1521_;
v_a_1518_ = v___x_1553_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_1540_);
lean_dec(v___x_1534_);
lean_del_object(v___x_1528_);
lean_dec(v_fst_1525_);
lean_del_object(v___x_1523_);
v_a_1517_ = v_tail_1521_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1537_);
lean_dec(v___x_1534_);
lean_del_object(v___x_1528_);
lean_dec(v_fst_1525_);
lean_del_object(v___x_1523_);
v_a_1517_ = v_tail_1521_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___boxed(lean_object* v___x_1565_, lean_object* v___x_1566_, lean_object* v___x_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
uint8_t v___x_17730__boxed_1570_; lean_object* v_res_1571_; 
v___x_17730__boxed_1570_ = lean_unbox(v___x_1567_);
v_res_1571_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v___x_1565_, v___x_1566_, v___x_17730__boxed_1570_, v_a_1568_, v_a_1569_);
lean_dec_ref(v___x_1565_);
return v_res_1571_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__0));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__2));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__4));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__6));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__8));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__11));
v___x_1591_ = l_Lean_stringToMessageData(v___x_1590_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_box(1);
v___x_1593_ = l_Lean_MessageData_ofFormat(v___x_1592_);
return v___x_1593_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__14));
v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object* v_type_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_inc_ref(v_type_1597_);
v___x_1603_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed), 6, 1);
lean_closure_set(v___x_1603_, 0, v_type_1597_);
v___x_1604_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1790_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1790_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1790_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v_env_1610_; lean_object* v___x_1611_; uint8_t v_isModule_1612_; 
v___x_1609_ = lean_st_ref_get(v_a_1601_);
v_env_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_env_1610_);
lean_dec(v___x_1609_);
v___x_1611_ = l_Lean_Environment_header(v_env_1610_);
lean_dec_ref(v_env_1610_);
v_isModule_1612_ = lean_ctor_get_uint8(v___x_1611_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1611_);
if (v_isModule_1612_ == 0)
{
lean_object* v___x_1614_; 
lean_dec_ref(v___x_1603_);
if (v_isShared_1608_ == 0)
{
v___x_1614_ = v___x_1607_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1605_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
else
{
lean_object* v___x_1616_; 
lean_del_object(v___x_1607_);
lean_inc_ref(v___x_1603_);
v___x_1616_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1603_, v_isModule_1612_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1778_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1778_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1778_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
uint8_t v___x_1621_; 
v___x_1621_ = lean_expr_eqv(v_a_1605_, v_a_1617_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v_toCold_1634_; lean_object* v_diag_1635_; lean_object* v_currRecDepth_1636_; lean_object* v_ref_1637_; uint8_t v_suppressElabErrors_1638_; uint8_t v_checkDeprecated_1639_; uint8_t v_isRecordingDeps_1640_; lean_object* v_fileName_1641_; lean_object* v_fileMap_1642_; lean_object* v_options_1643_; lean_object* v_currNamespace_1644_; lean_object* v_openDecls_1645_; lean_object* v_initHeartbeats_1646_; lean_object* v_maxHeartbeats_1647_; lean_object* v_quotContext_1648_; lean_object* v_currMacroScope_1649_; lean_object* v_cancelTk_x3f_1650_; lean_object* v_inheritedTraceOptions_1651_; lean_object* v_a_1653_; lean_object* v_a_1699_; lean_object* v___y_1711_; uint16_t v___y_1712_; lean_object* v_fileName_1713_; lean_object* v_fileMap_1714_; lean_object* v_currNamespace_1715_; lean_object* v_openDecls_1716_; lean_object* v_initHeartbeats_1717_; lean_object* v_maxHeartbeats_1718_; lean_object* v_quotContext_1719_; lean_object* v_currMacroScope_1720_; lean_object* v_cancelTk_x3f_1721_; lean_object* v_inheritedTraceOptions_1722_; lean_object* v_currRecDepth_1723_; lean_object* v_ref_1724_; uint8_t v_suppressElabErrors_1725_; uint8_t v_checkDeprecated_1726_; uint8_t v_isRecordingDeps_1727_; lean_object* v___y_1728_; uint8_t v___y_1738_; lean_object* v___y_1739_; uint16_t v___y_1740_; lean_object* v___y_1763_; 
lean_del_object(v___x_1619_);
v___x_1622_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__1, &l_Lean_Compiler_LCNF_toLCNFType___closed__1_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1);
v___x_1623_ = l_Lean_MessageData_ofExpr(v_a_1605_);
v___x_1624_ = l_Lean_indentD(v___x_1623_);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1622_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__3, &l_Lean_Compiler_LCNF_toLCNFType___closed__3_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3);
v___x_1627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = l_Lean_MessageData_ofExpr(v_a_1617_);
v___x_1629_ = l_Lean_indentD(v___x_1628_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1627_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__5, &l_Lean_Compiler_LCNF_toLCNFType___closed__5_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_st_ref_get(v_a_1599_);
v_toCold_1634_ = lean_ctor_get(v_a_1600_, 0);
v_diag_1635_ = lean_ctor_get(v___x_1633_, 4);
lean_inc_ref(v_diag_1635_);
lean_dec(v___x_1633_);
v_currRecDepth_1636_ = lean_ctor_get(v_a_1600_, 1);
v_ref_1637_ = lean_ctor_get(v_a_1600_, 2);
v_suppressElabErrors_1638_ = lean_ctor_get_uint8(v_a_1600_, sizeof(void*)*3 + 2);
v_checkDeprecated_1639_ = lean_ctor_get_uint8(v_a_1600_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1640_ = lean_ctor_get_uint8(v_a_1600_, sizeof(void*)*3 + 4);
v_fileName_1641_ = lean_ctor_get(v_toCold_1634_, 0);
v_fileMap_1642_ = lean_ctor_get(v_toCold_1634_, 1);
v_options_1643_ = lean_ctor_get(v_toCold_1634_, 2);
v_currNamespace_1644_ = lean_ctor_get(v_toCold_1634_, 4);
v_openDecls_1645_ = lean_ctor_get(v_toCold_1634_, 5);
v_initHeartbeats_1646_ = lean_ctor_get(v_toCold_1634_, 6);
v_maxHeartbeats_1647_ = lean_ctor_get(v_toCold_1634_, 7);
v_quotContext_1648_ = lean_ctor_get(v_toCold_1634_, 8);
v_currMacroScope_1649_ = lean_ctor_get(v_toCold_1634_, 9);
v_cancelTk_x3f_1650_ = lean_ctor_get(v_toCold_1634_, 10);
v_inheritedTraceOptions_1651_ = lean_ctor_get(v_toCold_1634_, 11);
if (v_isRecordingDeps_1640_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1643_);
v___x_1773_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v_options_1643_, v___x_1772_, v_isModule_1612_);
v___y_1763_ = v___x_1773_;
goto v___jp_1762_;
}
else
{
lean_object* v___x_1774_; 
lean_inc_ref(v_options_1643_);
v___x_1774_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1643_);
v___y_1763_ = v___x_1774_;
goto v___jp_1762_;
}
v___jp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v_snd_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1675_; 
lean_inc_ref(v_a_1653_);
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_a_1653_);
v___x_1655_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1599_, v_diag_1635_, v___x_1654_);
lean_dec_ref_known(v___x_1654_, 1);
lean_dec_ref(v___x_1655_);
v_snd_1656_ = lean_ctor_get(v_a_1653_, 1);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_a_1653_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v_a_1653_, 0);
lean_dec(v_unused_1676_);
v___x_1658_ = v_a_1653_;
v_isShared_1659_ = v_isSharedCheck_1675_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_snd_1656_);
lean_dec(v_a_1653_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1675_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__7, &l_Lean_Compiler_LCNF_toLCNFType___closed__7_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7);
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 7);
lean_ctor_set(v___x_1658_, 0, v___x_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_snd_1656_);
v___x_1662_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v___x_1663_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__9, &l_Lean_Compiler_LCNF_toLCNFType___closed__9_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_1664_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
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
}
v___jp_1677_:
{
lean_object* v___x_1678_; lean_object* v_env_1679_; lean_object* v___x_1680_; lean_object* v_diag_1681_; lean_object* v_unfoldAxiomCounter_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1678_ = lean_st_ref_get(v_a_1601_);
v_env_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_ref(v_env_1679_);
lean_dec(v___x_1678_);
v___x_1680_ = lean_st_ref_get(v_a_1599_);
v_diag_1681_ = lean_ctor_get(v___x_1680_, 4);
lean_inc_ref(v_diag_1681_);
lean_dec(v___x_1680_);
v_unfoldAxiomCounter_1682_ = lean_ctor_get(v_diag_1681_, 1);
lean_inc_ref(v_unfoldAxiomCounter_1682_);
lean_dec_ref(v_diag_1681_);
v___x_1683_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_unfoldAxiomCounter_1682_);
lean_dec_ref(v_unfoldAxiomCounter_1682_);
v___x_1684_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__10));
v___x_1685_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v_diag_1635_, v_env_1679_, v___x_1621_, v___x_1683_, v___x_1684_);
v___x_1686_ = l_List_isEmpty___redArg(v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec_ref_known(v___x_1632_, 2);
v___x_1687_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__12, &l_Lean_Compiler_LCNF_toLCNFType___closed__12_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12);
v___x_1688_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__13, &l_Lean_Compiler_LCNF_toLCNFType___closed__13_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13);
v___x_1689_ = l_Lean_MessageData_joinSep(v___x_1685_, v___x_1688_);
v___x_1690_ = l_Lean_indentD(v___x_1689_);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1687_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__15, &l_Lean_Compiler_LCNF_toLCNFType___closed__15_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = lean_box(0);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___x_1693_);
v_a_1653_ = v___x_1695_;
goto v___jp_1652_;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v___x_1685_);
v___x_1696_ = lean_box(0);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___x_1632_);
v_a_1653_ = v___x_1697_;
goto v___jp_1652_;
}
}
v___jp_1698_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
v___x_1700_ = lean_box(0);
v___x_1701_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1599_, v_diag_1635_, v___x_1700_);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v___x_1701_, 0);
lean_dec(v_unused_1709_);
v___x_1703_ = v___x_1701_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v___x_1701_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 1);
lean_ctor_set(v___x_1703_, 0, v_a_1699_);
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1699_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
v___jp_1710_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1729_ = l_Lean_maxRecDepth;
v___x_1730_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v___y_1711_, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1731_, 0, v_fileName_1713_);
lean_ctor_set(v___x_1731_, 1, v_fileMap_1714_);
lean_ctor_set(v___x_1731_, 2, v___y_1711_);
lean_ctor_set(v___x_1731_, 3, v___x_1730_);
lean_ctor_set(v___x_1731_, 4, v_currNamespace_1715_);
lean_ctor_set(v___x_1731_, 5, v_openDecls_1716_);
lean_ctor_set(v___x_1731_, 6, v_initHeartbeats_1717_);
lean_ctor_set(v___x_1731_, 7, v_maxHeartbeats_1718_);
lean_ctor_set(v___x_1731_, 8, v_quotContext_1719_);
lean_ctor_set(v___x_1731_, 9, v_currMacroScope_1720_);
lean_ctor_set(v___x_1731_, 10, v_cancelTk_x3f_1721_);
lean_ctor_set(v___x_1731_, 11, v_inheritedTraceOptions_1722_);
lean_inc(v_ref_1724_);
lean_inc(v_currRecDepth_1723_);
v___x_1732_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
lean_ctor_set(v___x_1732_, 1, v_currRecDepth_1723_);
lean_ctor_set(v___x_1732_, 2, v_ref_1724_);
lean_ctor_set_uint16(v___x_1732_, sizeof(void*)*3, v___y_1712_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 2, v_suppressElabErrors_1725_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 3, v_checkDeprecated_1726_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 4, v_isRecordingDeps_1727_);
v___x_1733_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1603_, v_isModule_1612_, v_a_1598_, v_a_1599_, v___x_1732_, v___y_1728_);
lean_dec_ref_known(v___x_1732_, 3);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_dec_ref_known(v___x_1733_, 1);
goto v___jp_1677_;
}
else
{
lean_object* v_a_1734_; uint8_t v___x_1735_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v___x_1735_ = l_Lean_Exception_isInterrupt(v_a_1734_);
if (v___x_1735_ == 0)
{
uint8_t v___x_1736_; 
lean_inc(v_a_1734_);
v___x_1736_ = l_Lean_Exception_isRuntime(v_a_1734_);
if (v___x_1736_ == 0)
{
lean_dec(v_a_1734_);
goto v___jp_1677_;
}
else
{
lean_dec_ref_known(v___x_1632_, 2);
v_a_1699_ = v_a_1734_;
goto v___jp_1698_;
}
}
else
{
lean_dec_ref_known(v___x_1632_, 2);
v_a_1699_ = v_a_1734_;
goto v___jp_1698_;
}
}
}
v___jp_1737_:
{
lean_object* v___x_1741_; lean_object* v_env_1742_; lean_object* v_nextMacroScope_1743_; lean_object* v_ngen_1744_; lean_object* v_auxDeclNGen_1745_; lean_object* v_traceState_1746_; lean_object* v_recordedDeps_1747_; lean_object* v_messages_1748_; lean_object* v_infoState_1749_; lean_object* v_snapshotTasks_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1760_; 
v___x_1741_ = lean_st_ref_take(v_a_1601_);
v_env_1742_ = lean_ctor_get(v___x_1741_, 0);
v_nextMacroScope_1743_ = lean_ctor_get(v___x_1741_, 1);
v_ngen_1744_ = lean_ctor_get(v___x_1741_, 2);
v_auxDeclNGen_1745_ = lean_ctor_get(v___x_1741_, 3);
v_traceState_1746_ = lean_ctor_get(v___x_1741_, 4);
v_recordedDeps_1747_ = lean_ctor_get(v___x_1741_, 6);
v_messages_1748_ = lean_ctor_get(v___x_1741_, 7);
v_infoState_1749_ = lean_ctor_get(v___x_1741_, 8);
v_snapshotTasks_1750_ = lean_ctor_get(v___x_1741_, 9);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v___x_1741_, 5);
lean_dec(v_unused_1761_);
v___x_1752_ = v___x_1741_;
v_isShared_1753_ = v_isSharedCheck_1760_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_snapshotTasks_1750_);
lean_inc(v_infoState_1749_);
lean_inc(v_messages_1748_);
lean_inc(v_recordedDeps_1747_);
lean_inc(v_traceState_1746_);
lean_inc(v_auxDeclNGen_1745_);
lean_inc(v_ngen_1744_);
lean_inc(v_nextMacroScope_1743_);
lean_inc(v_env_1742_);
lean_dec(v___x_1741_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1760_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1754_ = l_Lean_Kernel_enableDiag(v_env_1742_, v___y_1738_);
v___x_1755_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 5, v___x_1755_);
lean_ctor_set(v___x_1752_, 0, v___x_1754_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_nextMacroScope_1743_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_ngen_1744_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_auxDeclNGen_1745_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_traceState_1746_);
lean_ctor_set(v_reuseFailAlloc_1759_, 5, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1759_, 6, v_recordedDeps_1747_);
lean_ctor_set(v_reuseFailAlloc_1759_, 7, v_messages_1748_);
lean_ctor_set(v_reuseFailAlloc_1759_, 8, v_infoState_1749_);
lean_ctor_set(v_reuseFailAlloc_1759_, 9, v_snapshotTasks_1750_);
v___x_1757_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_st_ref_put(v_a_1601_, v___x_1757_);
lean_inc_ref(v_inheritedTraceOptions_1651_);
lean_inc(v_cancelTk_x3f_1650_);
lean_inc(v_currMacroScope_1649_);
lean_inc(v_quotContext_1648_);
lean_inc(v_maxHeartbeats_1647_);
lean_inc(v_initHeartbeats_1646_);
lean_inc(v_openDecls_1645_);
lean_inc(v_currNamespace_1644_);
lean_inc_ref(v_fileMap_1642_);
lean_inc_ref(v_fileName_1641_);
v___y_1711_ = v___y_1739_;
v___y_1712_ = v___y_1740_;
v_fileName_1713_ = v_fileName_1641_;
v_fileMap_1714_ = v_fileMap_1642_;
v_currNamespace_1715_ = v_currNamespace_1644_;
v_openDecls_1716_ = v_openDecls_1645_;
v_initHeartbeats_1717_ = v_initHeartbeats_1646_;
v_maxHeartbeats_1718_ = v_maxHeartbeats_1647_;
v_quotContext_1719_ = v_quotContext_1648_;
v_currMacroScope_1720_ = v_currMacroScope_1649_;
v_cancelTk_x3f_1721_ = v_cancelTk_x3f_1650_;
v_inheritedTraceOptions_1722_ = v_inheritedTraceOptions_1651_;
v_currRecDepth_1723_ = v_currRecDepth_1636_;
v_ref_1724_ = v_ref_1637_;
v_suppressElabErrors_1725_ = v_suppressElabErrors_1638_;
v_checkDeprecated_1726_ = v_checkDeprecated_1639_;
v_isRecordingDeps_1727_ = v_isRecordingDeps_1640_;
v___y_1728_ = v_a_1601_;
goto v___jp_1710_;
}
}
}
v___jp_1762_:
{
uint16_t v___x_1764_; lean_object* v___x_1765_; lean_object* v_env_1766_; uint8_t v___x_1767_; uint16_t v___x_1768_; uint16_t v___x_1769_; uint16_t v___x_1770_; uint8_t v___x_1771_; 
v___x_1764_ = l_Lean_OptionFlags_ofOptions(v___y_1763_);
v___x_1765_ = lean_st_ref_get(v_a_1601_);
v_env_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc_ref(v_env_1766_);
lean_dec(v___x_1765_);
v___x_1767_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1766_);
lean_dec_ref(v_env_1766_);
v___x_1768_ = 512;
v___x_1769_ = lean_uint16_land(v___x_1764_, v___x_1768_);
v___x_1770_ = 0;
v___x_1771_ = lean_uint16_dec_eq(v___x_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
if (v___x_1767_ == 0)
{
v___y_1738_ = v_isModule_1612_;
v___y_1739_ = v___y_1763_;
v___y_1740_ = v___x_1764_;
goto v___jp_1737_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1651_);
lean_inc(v_cancelTk_x3f_1650_);
lean_inc(v_currMacroScope_1649_);
lean_inc(v_quotContext_1648_);
lean_inc(v_maxHeartbeats_1647_);
lean_inc(v_initHeartbeats_1646_);
lean_inc(v_openDecls_1645_);
lean_inc(v_currNamespace_1644_);
lean_inc_ref(v_fileMap_1642_);
lean_inc_ref(v_fileName_1641_);
v___y_1711_ = v___y_1763_;
v___y_1712_ = v___x_1764_;
v_fileName_1713_ = v_fileName_1641_;
v_fileMap_1714_ = v_fileMap_1642_;
v_currNamespace_1715_ = v_currNamespace_1644_;
v_openDecls_1716_ = v_openDecls_1645_;
v_initHeartbeats_1717_ = v_initHeartbeats_1646_;
v_maxHeartbeats_1718_ = v_maxHeartbeats_1647_;
v_quotContext_1719_ = v_quotContext_1648_;
v_currMacroScope_1720_ = v_currMacroScope_1649_;
v_cancelTk_x3f_1721_ = v_cancelTk_x3f_1650_;
v_inheritedTraceOptions_1722_ = v_inheritedTraceOptions_1651_;
v_currRecDepth_1723_ = v_currRecDepth_1636_;
v_ref_1724_ = v_ref_1637_;
v_suppressElabErrors_1725_ = v_suppressElabErrors_1638_;
v_checkDeprecated_1726_ = v_checkDeprecated_1639_;
v_isRecordingDeps_1727_ = v_isRecordingDeps_1640_;
v___y_1728_ = v_a_1601_;
goto v___jp_1710_;
}
}
else
{
if (v___x_1767_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1651_);
lean_inc(v_cancelTk_x3f_1650_);
lean_inc(v_currMacroScope_1649_);
lean_inc(v_quotContext_1648_);
lean_inc(v_maxHeartbeats_1647_);
lean_inc(v_initHeartbeats_1646_);
lean_inc(v_openDecls_1645_);
lean_inc(v_currNamespace_1644_);
lean_inc_ref(v_fileMap_1642_);
lean_inc_ref(v_fileName_1641_);
v___y_1711_ = v___y_1763_;
v___y_1712_ = v___x_1764_;
v_fileName_1713_ = v_fileName_1641_;
v_fileMap_1714_ = v_fileMap_1642_;
v_currNamespace_1715_ = v_currNamespace_1644_;
v_openDecls_1716_ = v_openDecls_1645_;
v_initHeartbeats_1717_ = v_initHeartbeats_1646_;
v_maxHeartbeats_1718_ = v_maxHeartbeats_1647_;
v_quotContext_1719_ = v_quotContext_1648_;
v_currMacroScope_1720_ = v_currMacroScope_1649_;
v_cancelTk_x3f_1721_ = v_cancelTk_x3f_1650_;
v_inheritedTraceOptions_1722_ = v_inheritedTraceOptions_1651_;
v_currRecDepth_1723_ = v_currRecDepth_1636_;
v_ref_1724_ = v_ref_1637_;
v_suppressElabErrors_1725_ = v_suppressElabErrors_1638_;
v_checkDeprecated_1726_ = v_checkDeprecated_1639_;
v_isRecordingDeps_1727_ = v_isRecordingDeps_1640_;
v___y_1728_ = v_a_1601_;
goto v___jp_1710_;
}
else
{
v___y_1738_ = v___x_1621_;
v___y_1739_ = v___y_1763_;
v___y_1740_ = v___x_1764_;
goto v___jp_1737_;
}
}
}
}
else
{
lean_object* v___x_1776_; 
lean_dec(v_a_1617_);
lean_dec_ref(v___x_1603_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v_a_1605_);
v___x_1776_ = v___x_1619_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1605_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; uint8_t v___x_1780_; 
lean_dec_ref(v___x_1603_);
v_a_1779_ = lean_ctor_get(v___x_1616_, 0);
v___x_1780_ = l_Lean_Exception_isInterrupt(v_a_1779_);
if (v___x_1780_ == 0)
{
uint8_t v___x_1781_; 
lean_inc(v_a_1779_);
v___x_1781_ = l_Lean_Exception_isRuntime(v_a_1779_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1789_);
v___x_1783_ = v___x_1616_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_dec(v___x_1616_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set_tag(v___x_1783_, 0);
lean_ctor_set(v___x_1783_, 0, v_a_1605_);
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1605_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_dec(v_a_1605_);
return v___x_1616_;
}
}
else
{
lean_dec(v_a_1605_);
return v___x_1616_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1603_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___boxed(lean_object* v_type_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Compiler_LCNF_toLCNFType(v_type_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object* v_00_u03b1_1798_, lean_object* v_x_1799_, uint8_t v_isExporting_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1799_, v_isExporting_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___boxed(lean_object* v_00_u03b1_1807_, lean_object* v_x_1808_, lean_object* v_isExporting_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
uint8_t v_isExporting_boxed_1815_; lean_object* v_res_1816_; 
v_isExporting_boxed_1815_ = lean_unbox(v_isExporting_1809_);
v_res_1816_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(v_00_u03b1_1807_, v_x_1808_, v_isExporting_boxed_1815_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(lean_object* v_00_u03b2_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1818_, v_x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___boxed(lean_object* v_00_u03b2_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(v_00_u03b2_1821_, v_x_1822_, v_x_1823_);
lean_dec(v_x_1823_);
lean_dec_ref(v_x_1822_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(lean_object* v_00_u03b2_1825_, lean_object* v_m_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___boxed(lean_object* v_00_u03b2_1828_, lean_object* v_m_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(v_00_u03b2_1828_, v_m_1829_);
lean_dec_ref(v_m_1829_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0___redArg();
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0_spec__0(lean_object* v_00_u03b2_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2(lean_object* v_00_u03b2_1839_, lean_object* v_x_1840_, size_t v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2___redArg(v_x_1840_, v_x_1841_, v_x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
size_t v_x_18241__boxed_1848_; lean_object* v_res_1849_; 
v_x_18241__boxed_1848_ = lean_unbox_usize(v_x_1846_);
lean_dec(v_x_1846_);
v_res_1849_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2(v_00_u03b2_1844_, v_x_1845_, v_x_18241__boxed_1848_, v_x_1847_);
lean_dec(v_x_1847_);
lean_dec_ref(v_x_1845_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4(lean_object* v_00_u03c3_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_map_1852_, lean_object* v_f_1853_, lean_object* v_init_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___redArg(v_map_1852_, v_f_1853_, v_init_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1856_, lean_object* v_00_u03b2_1857_, lean_object* v_map_1858_, lean_object* v_f_1859_, lean_object* v_init_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4(v_00_u03c3_1856_, v_00_u03b2_1857_, v_map_1858_, v_f_1859_, v_init_1860_);
lean_dec_ref(v_map_1858_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1862_, lean_object* v_keys_1863_, lean_object* v_vals_1864_, lean_object* v_heq_1865_, lean_object* v_i_1866_, lean_object* v_k_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5___redArg(v_keys_1863_, v_vals_1864_, v_i_1866_, v_k_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1869_, lean_object* v_keys_1870_, lean_object* v_vals_1871_, lean_object* v_heq_1872_, lean_object* v_i_1873_, lean_object* v_k_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__2_spec__5(v_00_u03b2_1869_, v_keys_1870_, v_vals_1871_, v_heq_1872_, v_i_1873_, v_k_1874_);
lean_dec(v_k_1874_);
lean_dec_ref(v_vals_1871_);
lean_dec_ref(v_keys_1870_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8___redArg(lean_object* v_map_1876_, lean_object* v_f_1877_, lean_object* v_init_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___redArg(v_f_1877_, v_map_1876_, v_init_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_map_1880_, lean_object* v_f_1881_, lean_object* v_init_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8___redArg(v_map_1880_, v_f_1881_, v_init_1882_);
lean_dec_ref(v_map_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8(lean_object* v_00_u03c3_1884_, lean_object* v_00_u03b2_1885_, lean_object* v_map_1886_, lean_object* v_f_1887_, lean_object* v_init_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___redArg(v_f_1887_, v_map_1886_, v_init_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03c3_1890_, lean_object* v_00_u03b2_1891_, lean_object* v_map_1892_, lean_object* v_f_1893_, lean_object* v_init_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8(v_00_u03c3_1890_, v_00_u03b2_1891_, v_map_1892_, v_f_1893_, v_init_1894_);
lean_dec_ref(v_map_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03c3_1896_, lean_object* v_00_u03b1_1897_, lean_object* v_00_u03b2_1898_, lean_object* v_f_1899_, lean_object* v_x_1900_, lean_object* v_x_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___redArg(v_f_1899_, v_x_1900_, v_x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03c3_1903_, lean_object* v_00_u03b1_1904_, lean_object* v_00_u03b2_1905_, lean_object* v_f_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12(v_00_u03c3_1903_, v_00_u03b1_1904_, v_00_u03b2_1905_, v_f_1906_, v_x_1907_, v_x_1908_);
lean_dec_ref(v_x_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13(lean_object* v_00_u03b1_1910_, lean_object* v_00_u03b2_1911_, lean_object* v_00_u03c3_1912_, lean_object* v_f_1913_, lean_object* v_as_1914_, size_t v_i_1915_, size_t v_stop_1916_, lean_object* v_b_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_f_1913_, v_as_1914_, v_i_1915_, v_stop_1916_, v_b_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13___boxed(lean_object* v_00_u03b1_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_00_u03c3_1921_, lean_object* v_f_1922_, lean_object* v_as_1923_, lean_object* v_i_1924_, lean_object* v_stop_1925_, lean_object* v_b_1926_){
_start:
{
size_t v_i_boxed_1927_; size_t v_stop_boxed_1928_; lean_object* v_res_1929_; 
v_i_boxed_1927_ = lean_unbox_usize(v_i_1924_);
lean_dec(v_i_1924_);
v_stop_boxed_1928_ = lean_unbox_usize(v_stop_1925_);
lean_dec(v_stop_1925_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__13(v_00_u03b1_1919_, v_00_u03b2_1920_, v_00_u03c3_1921_, v_f_1922_, v_as_1923_, v_i_boxed_1927_, v_stop_boxed_1928_, v_b_1926_);
lean_dec_ref(v_as_1923_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14(lean_object* v_00_u03c3_1930_, lean_object* v_00_u03b1_1931_, lean_object* v_00_u03b2_1932_, lean_object* v_f_1933_, lean_object* v_keys_1934_, lean_object* v_vals_1935_, lean_object* v_heq_1936_, lean_object* v_i_1937_, lean_object* v_acc_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14___redArg(v_f_1933_, v_keys_1934_, v_vals_1935_, v_i_1937_, v_acc_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14___boxed(lean_object* v_00_u03c3_1940_, lean_object* v_00_u03b1_1941_, lean_object* v_00_u03b2_1942_, lean_object* v_f_1943_, lean_object* v_keys_1944_, lean_object* v_vals_1945_, lean_object* v_heq_1946_, lean_object* v_i_1947_, lean_object* v_acc_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__4_spec__8_spec__12_spec__14(v_00_u03c3_1940_, v_00_u03b1_1941_, v_00_u03b2_1942_, v_f_1943_, v_keys_1944_, v_vals_1945_, v_heq_1946_, v_i_1947_, v_acc_1948_);
lean_dec_ref(v_vals_1945_);
lean_dec_ref(v_keys_1944_);
return v_res_1949_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f(lean_object* v_a_1954_, lean_object* v_b_1955_){
_start:
{
uint8_t v___x_1962_; 
v___x_1962_ = l_Lean_Expr_isErased(v_a_1954_);
if (v___x_1962_ == 0)
{
uint8_t v___x_1963_; 
v___x_1963_ = l_Lean_Expr_isErased(v_b_1955_);
if (v___x_1963_ == 0)
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_expr_eqv(v_a_1954_, v_b_1955_);
if (v___x_1964_ == 0)
{
lean_object* v_a_x27_1965_; lean_object* v_b_x27_1966_; uint8_t v___x_1967_; 
lean_inc_ref(v_a_1954_);
v_a_x27_1965_ = l_Lean_Expr_headBeta(v_a_1954_);
lean_inc_ref(v_b_1955_);
v_b_x27_1966_ = l_Lean_Expr_headBeta(v_b_1955_);
v___x_1967_ = lean_expr_eqv(v_a_1954_, v_a_x27_1965_);
if (v___x_1967_ == 0)
{
lean_dec_ref(v_b_1955_);
lean_dec_ref(v_a_1954_);
v_a_1954_ = v_a_x27_1965_;
v_b_1955_ = v_b_x27_1966_;
goto _start;
}
else
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_expr_eqv(v_b_1955_, v_b_x27_1966_);
if (v___x_1969_ == 0)
{
lean_dec_ref(v_b_1955_);
lean_dec_ref(v_a_1954_);
v_a_1954_ = v_a_x27_1965_;
v_b_1955_ = v_b_x27_1966_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_1966_);
lean_dec_ref(v_a_x27_1965_);
switch(lean_obj_tag(v_a_1954_))
{
case 10:
{
lean_object* v_expr_1971_; 
v_expr_1971_ = lean_ctor_get(v_a_1954_, 1);
lean_inc_ref(v_expr_1971_);
lean_dec_ref_known(v_a_1954_, 2);
v_a_1954_ = v_expr_1971_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_1955_))
{
case 10:
{
lean_object* v_expr_1973_; 
v_expr_1973_ = lean_ctor_get(v_b_1955_, 1);
lean_inc_ref(v_expr_1973_);
lean_dec_ref_known(v_b_1955_, 2);
v_b_1955_ = v_expr_1973_;
goto _start;
}
case 5:
{
lean_object* v_fn_1975_; lean_object* v_arg_1976_; lean_object* v_fn_1977_; lean_object* v_arg_1978_; lean_object* v___x_1979_; 
v_fn_1975_ = lean_ctor_get(v_a_1954_, 0);
lean_inc_ref(v_fn_1975_);
v_arg_1976_ = lean_ctor_get(v_a_1954_, 1);
lean_inc_ref(v_arg_1976_);
lean_dec_ref_known(v_a_1954_, 2);
v_fn_1977_ = lean_ctor_get(v_b_1955_, 0);
lean_inc_ref(v_fn_1977_);
v_arg_1978_ = lean_ctor_get(v_b_1955_, 1);
lean_inc_ref(v_arg_1978_);
lean_dec_ref_known(v_b_1955_, 2);
v___x_1979_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_fn_1975_, v_fn_1977_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_dec_ref(v_arg_1978_);
lean_dec_ref(v_arg_1976_);
goto v___jp_1960_;
}
else
{
lean_object* v_val_1980_; lean_object* v___x_1981_; 
v_val_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_val_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v___x_1981_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_arg_1976_, v_arg_1978_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_dec(v_val_1980_);
goto v___jp_1960_;
}
else
{
lean_object* v_val_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1990_; 
v_val_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_val_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = l_Lean_Expr_app___override(v_val_1980_, v_val_1982_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1986_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_1954_, 2);
lean_dec_ref(v_b_1955_);
goto v___jp_1958_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_1955_))
{
case 10:
{
lean_object* v_expr_1991_; 
v_expr_1991_ = lean_ctor_get(v_b_1955_, 1);
lean_inc_ref(v_expr_1991_);
lean_dec_ref_known(v_b_1955_, 2);
v_b_1955_ = v_expr_1991_;
goto _start;
}
case 7:
{
lean_object* v_binderName_1993_; lean_object* v_binderType_1994_; lean_object* v_body_1995_; lean_object* v_binderType_1996_; lean_object* v_body_1997_; lean_object* v___x_1998_; 
v_binderName_1993_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_binderName_1993_);
v_binderType_1994_ = lean_ctor_get(v_a_1954_, 1);
lean_inc_ref(v_binderType_1994_);
v_body_1995_ = lean_ctor_get(v_a_1954_, 2);
lean_inc_ref(v_body_1995_);
lean_dec_ref_known(v_a_1954_, 3);
v_binderType_1996_ = lean_ctor_get(v_b_1955_, 1);
lean_inc_ref(v_binderType_1996_);
v_body_1997_ = lean_ctor_get(v_b_1955_, 2);
lean_inc_ref(v_body_1997_);
lean_dec_ref_known(v_b_1955_, 3);
v___x_1998_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_1994_, v_binderType_1996_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_1999_; 
lean_dec_ref(v_body_1997_);
lean_dec_ref(v_body_1995_);
lean_dec(v_binderName_1993_);
v___x_1999_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1);
return v___x_1999_;
}
else
{
lean_object* v_val_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2010_; 
v_val_2000_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2002_ = v___x_1998_;
v_isShared_2003_ = v_isSharedCheck_2010_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_val_2000_);
lean_dec(v___x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2010_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; uint8_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2004_ = l_Lean_Compiler_LCNF_joinTypes(v_body_1995_, v_body_1997_);
v___x_2005_ = 0;
v___x_2006_ = l_Lean_Expr_forallE___override(v_binderName_1993_, v_val_2000_, v___x_2004_, v___x_2005_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2006_);
v___x_2008_ = v___x_2002_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_1954_, 3);
lean_dec_ref(v_b_1955_);
goto v___jp_1958_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_1955_))
{
case 10:
{
lean_object* v_expr_2011_; 
v_expr_2011_ = lean_ctor_get(v_b_1955_, 1);
lean_inc_ref(v_expr_2011_);
lean_dec_ref_known(v_b_1955_, 2);
v_b_1955_ = v_expr_2011_;
goto _start;
}
case 6:
{
lean_object* v_binderName_2013_; lean_object* v_binderType_2014_; lean_object* v_body_2015_; lean_object* v_binderType_2016_; lean_object* v_body_2017_; lean_object* v___x_2018_; 
v_binderName_2013_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_binderName_2013_);
v_binderType_2014_ = lean_ctor_get(v_a_1954_, 1);
lean_inc_ref(v_binderType_2014_);
v_body_2015_ = lean_ctor_get(v_a_1954_, 2);
lean_inc_ref(v_body_2015_);
lean_dec_ref_known(v_a_1954_, 3);
v_binderType_2016_ = lean_ctor_get(v_b_1955_, 1);
lean_inc_ref(v_binderType_2016_);
v_body_2017_ = lean_ctor_get(v_b_1955_, 2);
lean_inc_ref(v_body_2017_);
lean_dec_ref_known(v_b_1955_, 3);
v___x_2018_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_2014_, v_binderType_2016_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; 
lean_dec_ref(v_body_2017_);
lean_dec_ref(v_body_2015_);
lean_dec(v_binderName_2013_);
v___x_2019_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1);
return v___x_2019_;
}
else
{
lean_object* v_val_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2030_; 
v_val_2020_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2022_ = v___x_2018_;
v_isShared_2023_ = v_isSharedCheck_2030_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_val_2020_);
lean_dec(v___x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2030_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2024_ = l_Lean_Compiler_LCNF_joinTypes(v_body_2015_, v_body_2017_);
v___x_2025_ = 0;
v___x_2026_ = l_Lean_Expr_lam___override(v_binderName_2013_, v_val_2020_, v___x_2024_, v___x_2025_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2026_);
v___x_2028_ = v___x_2022_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_1954_, 3);
lean_dec_ref(v_b_1955_);
goto v___jp_1958_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_1955_) == 10)
{
lean_object* v_expr_2031_; 
v_expr_2031_ = lean_ctor_get(v_b_1955_, 1);
lean_inc_ref(v_expr_2031_);
lean_dec_ref_known(v_b_1955_, 2);
v_b_1955_ = v_expr_2031_;
goto _start;
}
else
{
lean_dec_ref(v_b_1955_);
lean_dec_ref(v_a_1954_);
goto v___jp_1958_;
}
}
}
}
}
}
else
{
lean_object* v___x_2033_; 
lean_dec_ref(v_b_1955_);
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_a_1954_);
return v___x_2033_;
}
}
else
{
lean_dec_ref(v_b_1955_);
lean_dec_ref(v_a_1954_);
goto v___jp_1956_;
}
}
else
{
lean_dec_ref(v_b_1955_);
lean_dec_ref(v_a_1954_);
goto v___jp_1956_;
}
v___jp_1956_:
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1957_;
}
v___jp_1958_:
{
lean_object* v___x_1959_; 
v___x_1959_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1);
return v___x_1959_;
}
v___jp_1960_:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object* v_a_2034_, lean_object* v_b_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_a_2034_, v_b_2035_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
return v___x_2037_;
}
else
{
lean_object* v_val_2038_; 
v_val_2038_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_val_2038_);
lean_dec_ref_known(v___x_2036_, 1);
return v_val_2038_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object* v_type_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_Expr_headBeta(v_type_2039_);
switch(lean_obj_tag(v___x_2040_))
{
case 3:
{
uint8_t v___x_2041_; 
lean_dec_ref_known(v___x_2040_, 1);
v___x_2041_ = 1;
return v___x_2041_;
}
case 7:
{
lean_object* v_body_2042_; 
v_body_2042_ = lean_ctor_get(v___x_2040_, 2);
lean_inc_ref(v_body_2042_);
lean_dec_ref_known(v___x_2040_, 3);
v_type_2039_ = v_body_2042_;
goto _start;
}
default: 
{
uint8_t v___x_2044_; 
lean_dec_ref(v___x_2040_);
v___x_2044_ = 0;
return v___x_2044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTypeFormerType___boxed(lean_object* v_type_2045_){
_start:
{
uint8_t v_res_2046_; lean_object* v_r_2047_; 
v_res_2046_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_2045_);
v_r_2047_ = lean_box(v_res_2046_);
return v_r_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(lean_object* v_msgData_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; lean_object* v_toCold_2053_; lean_object* v_env_2054_; lean_object* v_options_2055_; uint8_t v___x_2056_; lean_object* v_env_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2052_ = lean_st_ref_get(v___y_2050_);
v_toCold_2053_ = lean_ctor_get(v___y_2049_, 0);
v_env_2054_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_ref(v_env_2054_);
lean_dec(v___x_2052_);
v_options_2055_ = lean_ctor_get(v_toCold_2053_, 2);
v___x_2056_ = 0;
v_env_2057_ = l_Lean_Environment_setRecordingDeps(v_env_2054_, v___x_2056_);
v___x_2058_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_2059_ = lean_unsigned_to_nat(32u);
v___x_2060_ = lean_mk_empty_array_with_capacity(v___x_2059_);
lean_dec_ref(v___x_2060_);
v___x_2061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_2055_);
v___x_2062_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2062_, 0, v_env_2057_);
lean_ctor_set(v___x_2062_, 1, v___x_2058_);
lean_ctor_set(v___x_2062_, 2, v___x_2061_);
lean_ctor_set(v___x_2062_, 3, v_options_2055_);
v___x_2063_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v_msgData_2048_);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0___boxed(lean_object* v_msgData_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msgData_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(lean_object* v_msg_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_ref_2074_; lean_object* v___x_2075_; lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2084_; 
v_ref_2074_ = lean_ctor_get(v___y_2071_, 2);
v___x_2075_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msg_2070_, v___y_2071_, v___y_2072_);
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
lean_inc(v_ref_2074_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v_ref_2074_);
lean_ctor_set(v___x_2080_, 1, v_a_2076_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 1);
lean_ctor_set(v___x_2078_, 0, v___x_2080_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg___boxed(lean_object* v_msg_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2089_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0));
v___x_2092_ = l_Lean_stringToMessageData(v___x_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(lean_object* v_ps_2093_, lean_object* v_i_2094_, lean_object* v_type_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = lean_array_get_size(v_ps_2093_);
v___x_2100_ = lean_nat_dec_lt(v_i_2094_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
lean_dec(v_i_2094_);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v_type_2095_);
return v___x_2101_;
}
else
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Expr_headBeta(v_type_2095_);
if (lean_obj_tag(v___x_2102_) == 7)
{
lean_object* v_body_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_body_2103_ = lean_ctor_get(v___x_2102_, 2);
lean_inc_ref(v_body_2103_);
lean_dec_ref_known(v___x_2102_, 3);
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = lean_nat_add(v_i_2094_, v___x_2104_);
v___x_2106_ = lean_array_fget_borrowed(v_ps_2093_, v_i_2094_);
lean_dec(v_i_2094_);
v___x_2107_ = lean_expr_instantiate1(v_body_2103_, v___x_2106_);
lean_dec_ref(v_body_2103_);
v_i_2094_ = v___x_2105_;
v_type_2095_ = v___x_2107_;
goto _start;
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec_ref(v___x_2102_);
lean_dec(v_i_2094_);
v___x_2109_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1);
v___x_2110_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v___x_2109_, v_a_2096_, v_a_2097_);
return v___x_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object* v_ps_2111_, lean_object* v_i_2112_, lean_object* v_type_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2111_, v_i_2112_, v_type_2113_, v_a_2114_, v_a_2115_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec_ref(v_ps_2111_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(lean_object* v_00_u03b1_2118_, lean_object* v_msg_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2119_, v___y_2120_, v___y_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___boxed(lean_object* v_00_u03b1_2124_, lean_object* v_msg_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(v_00_u03b1_2124_, v_msg_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter___redArg(lean_object* v_e_2130_, lean_object* v_h__1_2131_, lean_object* v_h__2_2132_){
_start:
{
if (lean_obj_tag(v_e_2130_) == 7)
{
lean_object* v_binderName_2133_; lean_object* v_binderType_2134_; lean_object* v_body_2135_; uint8_t v_binderInfo_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec(v_h__2_2132_);
v_binderName_2133_ = lean_ctor_get(v_e_2130_, 0);
lean_inc(v_binderName_2133_);
v_binderType_2134_ = lean_ctor_get(v_e_2130_, 1);
lean_inc_ref(v_binderType_2134_);
v_body_2135_ = lean_ctor_get(v_e_2130_, 2);
lean_inc_ref(v_body_2135_);
v_binderInfo_2136_ = lean_ctor_get_uint8(v_e_2130_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2130_, 3);
v___x_2137_ = lean_box(v_binderInfo_2136_);
v___x_2138_ = lean_apply_4(v_h__1_2131_, v_binderName_2133_, v_binderType_2134_, v_body_2135_, v___x_2137_);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; 
lean_dec(v_h__1_2131_);
v___x_2139_ = lean_apply_2(v_h__2_2132_, v_e_2130_, lean_box(0));
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter(lean_object* v_motive_2140_, lean_object* v_e_2141_, lean_object* v_h__1_2142_, lean_object* v_h__2_2143_){
_start:
{
if (lean_obj_tag(v_e_2141_) == 7)
{
lean_object* v_binderName_2144_; lean_object* v_binderType_2145_; lean_object* v_body_2146_; uint8_t v_binderInfo_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec(v_h__2_2143_);
v_binderName_2144_ = lean_ctor_get(v_e_2141_, 0);
lean_inc(v_binderName_2144_);
v_binderType_2145_ = lean_ctor_get(v_e_2141_, 1);
lean_inc_ref(v_binderType_2145_);
v_body_2146_ = lean_ctor_get(v_e_2141_, 2);
lean_inc_ref(v_body_2146_);
v_binderInfo_2147_ = lean_ctor_get_uint8(v_e_2141_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2141_, 3);
v___x_2148_ = lean_box(v_binderInfo_2147_);
v___x_2149_ = lean_apply_4(v_h__1_2142_, v_binderName_2144_, v_binderType_2145_, v_body_2146_, v___x_2148_);
return v___x_2149_;
}
else
{
lean_object* v___x_2150_; 
lean_dec(v_h__1_2142_);
v___x_2150_ = lean_apply_2(v_h__2_2143_, v_e_2141_, lean_box(0));
return v___x_2150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object* v_type_2151_, lean_object* v_ps_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2152_, v___x_2156_, v_type_2151_, v_a_2153_, v_a_2154_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object* v_type_2158_, lean_object* v_ps_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_2158_, v_ps_2159_, v_a_2160_, v_a_2161_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_ps_2159_);
return v_res_2163_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object* v_type_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_Expr_headBeta(v_type_2164_);
switch(lean_obj_tag(v___x_2165_))
{
case 3:
{
lean_object* v_u_2166_; 
v_u_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_u_2166_);
lean_dec_ref_known(v___x_2165_, 1);
if (lean_obj_tag(v_u_2166_) == 0)
{
uint8_t v___x_2167_; 
v___x_2167_ = 1;
return v___x_2167_;
}
else
{
uint8_t v___x_2168_; 
lean_dec(v_u_2166_);
v___x_2168_ = 0;
return v___x_2168_;
}
}
case 7:
{
lean_object* v_body_2169_; 
v_body_2169_ = lean_ctor_get(v___x_2165_, 2);
lean_inc_ref(v_body_2169_);
lean_dec_ref_known(v___x_2165_, 3);
v_type_2164_ = v_body_2169_;
goto _start;
}
default: 
{
uint8_t v___x_2171_; 
lean_dec_ref(v___x_2165_);
v___x_2171_ = 0;
return v___x_2171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPredicateType___boxed(lean_object* v_type_2172_){
_start:
{
uint8_t v_res_2173_; lean_object* v_r_2174_; 
v_res_2173_ = l_Lean_Compiler_LCNF_isPredicateType(v_type_2172_);
v_r_2174_ = lean_box(v_res_2173_);
return v_r_2174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_maybeTypeFormerType(lean_object* v_type_2175_){
_start:
{
lean_object* v___x_2176_; 
lean_inc_ref(v_type_2175_);
v___x_2176_ = l_Lean_Expr_headBeta(v_type_2175_);
switch(lean_obj_tag(v___x_2176_))
{
case 3:
{
uint8_t v___x_2177_; 
lean_dec_ref_known(v___x_2176_, 1);
lean_dec_ref(v_type_2175_);
v___x_2177_ = 1;
return v___x_2177_;
}
case 7:
{
lean_object* v_body_2178_; 
lean_dec_ref(v_type_2175_);
v_body_2178_ = lean_ctor_get(v___x_2176_, 2);
lean_inc_ref(v_body_2178_);
lean_dec_ref_known(v___x_2176_, 3);
v_type_2175_ = v_body_2178_;
goto _start;
}
default: 
{
uint8_t v___x_2180_; 
lean_dec_ref(v___x_2176_);
v___x_2180_ = l_Lean_Expr_isErased(v_type_2175_);
lean_dec_ref(v_type_2175_);
return v___x_2180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_maybeTypeFormerType___boxed(lean_object* v_type_2181_){
_start:
{
uint8_t v_res_2182_; lean_object* v_r_2183_; 
v_res_2182_ = l_Lean_Compiler_LCNF_maybeTypeFormerType(v_type_2181_);
v_r_2183_ = lean_box(v_res_2182_);
return v_r_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object* v_type_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_Expr_getAppFn(v_type_2184_);
if (lean_obj_tag(v___x_2187_) == 4)
{
lean_object* v_declName_2188_; lean_object* v___x_2189_; lean_object* v_env_2190_; uint8_t v___x_2191_; 
v_declName_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_declName_2188_);
lean_dec_ref_known(v___x_2187_, 2);
v___x_2189_ = lean_st_ref_get(v_a_2185_);
v_env_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc_ref(v_env_2190_);
lean_dec(v___x_2189_);
v___x_2191_ = l_Lean_isClass(v_env_2190_, v_declName_2188_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec(v_declName_2188_);
v___x_2192_ = lean_box(0);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v_declName_2188_);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref(v___x_2187_);
v___x_2196_ = lean_box(0);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg___boxed(lean_object* v_type_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2198_, v_a_2199_);
lean_dec(v_a_2199_);
lean_dec_ref(v_type_2198_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object* v_type_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2202_, v_a_2204_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___boxed(lean_object* v_type_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Compiler_LCNF_isClass_x3f(v_type_2207_, v_a_2208_, v_a_2209_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec_ref(v_type_2207_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object* v_type_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2215_; 
lean_inc_ref(v_type_2212_);
v___x_2215_ = l_Lean_Expr_headBeta(v_type_2212_);
if (lean_obj_tag(v___x_2215_) == 7)
{
lean_object* v_body_2216_; 
lean_dec_ref(v_type_2212_);
v_body_2216_ = lean_ctor_get(v___x_2215_, 2);
lean_inc_ref(v_body_2216_);
lean_dec_ref_known(v___x_2215_, 3);
v_type_2212_ = v_body_2216_;
goto _start;
}
else
{
lean_object* v___x_2218_; 
lean_dec_ref(v___x_2215_);
v___x_2218_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2212_, v_a_2213_);
lean_dec_ref(v_type_2212_);
return v___x_2218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg___boxed(lean_object* v_type_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2219_, v_a_2220_);
lean_dec(v_a_2220_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object* v_type_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2223_, v_a_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___boxed(lean_object* v_type_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Compiler_LCNF_isArrowClass_x3f(v_type_2228_, v_a_2229_, v_a_2230_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object* v_e_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_Expr_headBeta(v_e_2233_);
if (lean_obj_tag(v___x_2234_) == 7)
{
lean_object* v_body_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v_body_2235_ = lean_ctor_get(v___x_2234_, 2);
lean_inc_ref(v_body_2235_);
lean_dec_ref_known(v___x_2234_, 3);
v___x_2236_ = l_Lean_Compiler_LCNF_getArrowArity(v_body_2235_);
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_add(v___x_2236_, v___x_2237_);
lean_dec(v___x_2236_);
return v___x_2238_;
}
else
{
lean_object* v___x_2239_; 
lean_dec_ref(v___x_2234_);
v___x_2239_ = lean_unsigned_to_nat(0u);
return v___x_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object* v_type_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Expr_getAppFn(v_type_2240_);
if (lean_obj_tag(v___x_2247_) == 4)
{
lean_object* v_declName_2248_; lean_object* v___x_2249_; lean_object* v_env_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; 
v_declName_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_declName_2248_);
lean_dec_ref_known(v___x_2247_, 2);
v___x_2249_ = lean_st_ref_get(v_a_2241_);
v_env_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc_ref(v_env_2250_);
lean_dec(v___x_2249_);
v___x_2251_ = 0;
v___x_2252_ = l_Lean_Environment_find_x3f(v_env_2250_, v_declName_2248_, v___x_2251_);
if (lean_obj_tag(v___x_2252_) == 1)
{
lean_object* v_val_2253_; 
v_val_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_val_2253_);
lean_dec_ref_known(v___x_2252_, 1);
if (lean_obj_tag(v_val_2253_) == 5)
{
lean_object* v_val_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2265_; 
v_val_2254_ = lean_ctor_get(v_val_2253_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_val_2253_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2256_ = v_val_2253_;
v_isShared_2257_ = v_isSharedCheck_2265_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_val_2254_);
lean_dec(v_val_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2265_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2258_ = l_Lean_InductiveVal_numCtors(v_val_2254_);
lean_dec_ref(v_val_2254_);
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = lean_nat_dec_eq(v___x_2258_, v___x_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(v___x_2260_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set_tag(v___x_2256_, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2261_);
v___x_2263_ = v___x_2256_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
else
{
lean_dec(v_val_2253_);
goto v___jp_2243_;
}
}
else
{
lean_dec(v___x_2252_);
goto v___jp_2243_;
}
}
else
{
uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_dec_ref(v___x_2247_);
v___x_2266_ = 0;
v___x_2267_ = lean_box(v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
v___jp_2243_:
{
uint8_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = 0;
v___x_2245_ = lean_box(v___x_2244_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg___boxed(lean_object* v_type_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2269_, v_a_2270_);
lean_dec(v_a_2270_);
lean_dec_ref(v_type_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object* v_type_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2273_, v_a_2275_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___boxed(lean_object* v_type_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors(v_type_2278_, v_a_2279_, v_a_2280_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec_ref(v_type_2278_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object* v_n_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2286_ = l_Lean_Name_str___override(v_n_2284_, v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isBoxedName(lean_object* v_name_2287_){
_start:
{
if (lean_obj_tag(v_name_2287_) == 1)
{
lean_object* v_str_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; 
v_str_2288_ = lean_ctor_get(v_name_2287_, 1);
v___x_2289_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2290_ = lean_string_dec_eq(v_str_2288_, v___x_2289_);
return v___x_2290_;
}
else
{
uint8_t v___x_2291_; 
v___x_2291_ = 0;
return v___x_2291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isBoxedName___boxed(lean_object* v_name_2292_){
_start:
{
uint8_t v_res_2293_; lean_object* v_r_2294_; 
v_res_2293_ = l_Lean_Compiler_LCNF_isBoxedName(v_name_2292_);
lean_dec(v_name_2292_);
v_r_2294_ = lean_box(v_res_2293_);
return v_r_2294_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_box(0);
v___x_2299_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__1));
v___x_2300_ = l_Lean_Expr_const___override(v___x_2299_, v___x_2298_);
return v___x_2300_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float(void){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_box(0);
v___x_2306_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__1));
v___x_2307_ = l_Lean_Expr_const___override(v___x_2306_, v___x_2305_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32(void){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2);
return v___x_2308_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_box(0);
v___x_2313_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1));
v___x_2314_ = l_Lean_Expr_const___override(v___x_2313_, v___x_2312_);
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8(void){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = lean_box(0);
v___x_2320_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1));
v___x_2321_ = l_Lean_Expr_const___override(v___x_2320_, v___x_2319_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16(void){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2326_ = lean_box(0);
v___x_2327_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1));
v___x_2328_ = l_Lean_Expr_const___override(v___x_2327_, v___x_2326_);
return v___x_2328_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32(void){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2);
return v___x_2329_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = lean_box(0);
v___x_2334_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1));
v___x_2335_ = l_Lean_Expr_const___override(v___x_2334_, v___x_2333_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64(void){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = lean_box(0);
v___x_2341_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__1));
v___x_2342_ = l_Lean_Expr_const___override(v___x_2341_, v___x_2340_);
return v___x_2342_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize(void){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_usize___closed__2, &l_Lean_Compiler_LCNF_ImpureType_usize___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2);
return v___x_2343_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = lean_box(0);
v___x_2345_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_2346_ = l_Lean_Expr_const___override(v___x_2345_, v___x_2344_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased(void){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_erased___closed__0, &l_Lean_Compiler_LCNF_ImpureType_erased___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = lean_box(0);
v___x_2352_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__1));
v___x_2353_ = l_Lean_Expr_const___override(v___x_2352_, v___x_2351_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object(void){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1));
v___x_2360_ = l_Lean_Expr_const___override(v___x_2359_, v___x_2358_);
return v___x_2360_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject(void){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2361_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1));
v___x_2367_ = l_Lean_Expr_const___override(v___x_2366_, v___x_2365_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged(void){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2368_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_2371_ = l_Lean_Expr_const___override(v___x_2370_, v___x_2369_);
return v___x_2371_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void(void){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_void___closed__0, &l_Lean_Compiler_LCNF_ImpureType_void___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0);
return v___x_2372_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object* v_x_2373_){
_start:
{
if (lean_obj_tag(v_x_2373_) == 4)
{
lean_object* v_declName_2374_; 
v_declName_2374_ = lean_ctor_get(v_x_2373_, 0);
if (lean_obj_tag(v_declName_2374_) == 1)
{
lean_object* v_pre_2375_; 
v_pre_2375_ = lean_ctor_get(v_declName_2374_, 0);
if (lean_obj_tag(v_pre_2375_) == 0)
{
lean_object* v_us_2376_; lean_object* v_str_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
v_us_2376_ = lean_ctor_get(v_x_2373_, 1);
v_str_2377_ = lean_ctor_get(v_declName_2374_, 1);
v___x_2378_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2379_ = lean_string_dec_eq(v_str_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2381_ = lean_string_dec_eq(v_str_2377_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2383_ = lean_string_dec_eq(v_str_2377_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2385_ = lean_string_dec_eq(v_str_2377_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0));
v___x_2387_ = lean_string_dec_eq(v_str_2377_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2389_ = lean_string_dec_eq(v_str_2377_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__0));
v___x_2391_ = lean_string_dec_eq(v_str_2377_, v___x_2390_);
if (v___x_2391_ == 0)
{
return v___x_2391_;
}
else
{
if (lean_obj_tag(v_us_2376_) == 0)
{
return v___x_2391_;
}
else
{
return v___x_2389_;
}
}
}
else
{
if (lean_obj_tag(v_us_2376_) == 0)
{
return v___x_2389_;
}
else
{
return v___x_2387_;
}
}
}
else
{
if (lean_obj_tag(v_us_2376_) == 0)
{
return v___x_2387_;
}
else
{
return v___x_2385_;
}
}
}
else
{
if (lean_obj_tag(v_us_2376_) == 0)
{
return v___x_2385_;
}
else
{
return v___x_2383_;
}
}
}
else
{
if (lean_obj_tag(v_us_2376_) == 0)
{
return v___x_2383_;
}
else
{
return v___x_2381_;
}
}
}
else
{
if (lean_obj_tag(v_us_2376_) == 0)
{
return v___x_2381_;
}
else
{
return v___x_2379_;
}
}
}
else
{
if (lean_obj_tag(v_us_2376_) == 0)
{
return v___x_2379_;
}
else
{
uint8_t v___x_2392_; 
v___x_2392_ = 0;
return v___x_2392_;
}
}
}
else
{
uint8_t v___x_2393_; 
v___x_2393_ = 0;
return v___x_2393_;
}
}
else
{
uint8_t v___x_2394_; 
v___x_2394_ = 0;
return v___x_2394_;
}
}
else
{
uint8_t v___x_2395_; 
v___x_2395_ = 0;
return v___x_2395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar___boxed(lean_object* v_x_2396_){
_start:
{
uint8_t v_res_2397_; lean_object* v_r_2398_; 
v_res_2397_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_x_2396_);
lean_dec_ref(v_x_2396_);
v_r_2398_ = lean_box(v_res_2397_);
return v_r_2398_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(lean_object* v_x_2399_){
_start:
{
if (lean_obj_tag(v_x_2399_) == 4)
{
lean_object* v_declName_2400_; 
v_declName_2400_ = lean_ctor_get(v_x_2399_, 0);
if (lean_obj_tag(v_declName_2400_) == 1)
{
lean_object* v_pre_2401_; 
v_pre_2401_ = lean_ctor_get(v_declName_2400_, 0);
if (lean_obj_tag(v_pre_2401_) == 0)
{
lean_object* v_us_2402_; lean_object* v_str_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v_us_2402_ = lean_ctor_get(v_x_2399_, 1);
v_str_2403_ = lean_ctor_get(v_declName_2400_, 1);
v___x_2404_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2405_ = lean_string_dec_eq(v_str_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2407_ = lean_string_dec_eq(v_str_2403_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2409_ = lean_string_dec_eq(v_str_2403_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2411_ = lean_string_dec_eq(v_str_2403_, v___x_2410_);
if (v___x_2411_ == 0)
{
return v___x_2411_;
}
else
{
if (lean_obj_tag(v_us_2402_) == 0)
{
return v___x_2411_;
}
else
{
return v___x_2409_;
}
}
}
else
{
if (lean_obj_tag(v_us_2402_) == 0)
{
return v___x_2409_;
}
else
{
return v___x_2407_;
}
}
}
else
{
if (lean_obj_tag(v_us_2402_) == 0)
{
return v___x_2407_;
}
else
{
return v___x_2405_;
}
}
}
else
{
if (lean_obj_tag(v_us_2402_) == 0)
{
return v___x_2405_;
}
else
{
uint8_t v___x_2412_; 
v___x_2412_ = 0;
return v___x_2412_;
}
}
}
else
{
uint8_t v___x_2413_; 
v___x_2413_ = 0;
return v___x_2413_;
}
}
else
{
uint8_t v___x_2414_; 
v___x_2414_ = 0;
return v___x_2414_;
}
}
else
{
uint8_t v___x_2415_; 
v___x_2415_ = 0;
return v___x_2415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj___boxed(lean_object* v_x_2416_){
_start:
{
uint8_t v_res_2417_; lean_object* v_r_2418_; 
v_res_2417_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(v_x_2416_);
lean_dec_ref(v_x_2416_);
v_r_2418_ = lean_box(v_res_2417_);
return v_r_2418_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object* v_x_2419_){
_start:
{
if (lean_obj_tag(v_x_2419_) == 4)
{
lean_object* v_declName_2420_; 
v_declName_2420_ = lean_ctor_get(v_x_2419_, 0);
if (lean_obj_tag(v_declName_2420_) == 1)
{
lean_object* v_pre_2421_; 
v_pre_2421_ = lean_ctor_get(v_declName_2420_, 0);
if (lean_obj_tag(v_pre_2421_) == 0)
{
lean_object* v_us_2422_; lean_object* v_str_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; 
v_us_2422_ = lean_ctor_get(v_x_2419_, 1);
v_str_2423_ = lean_ctor_get(v_declName_2420_, 1);
v___x_2424_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2425_ = lean_string_dec_eq(v_str_2423_, v___x_2424_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2427_ = lean_string_dec_eq(v_str_2423_, v___x_2426_);
if (v___x_2427_ == 0)
{
return v___x_2427_;
}
else
{
if (lean_obj_tag(v_us_2422_) == 0)
{
return v___x_2427_;
}
else
{
return v___x_2425_;
}
}
}
else
{
if (lean_obj_tag(v_us_2422_) == 0)
{
return v___x_2425_;
}
else
{
uint8_t v___x_2428_; 
v___x_2428_ = 0;
return v___x_2428_;
}
}
}
else
{
uint8_t v___x_2429_; 
v___x_2429_ = 0;
return v___x_2429_;
}
}
else
{
uint8_t v___x_2430_; 
v___x_2430_ = 0;
return v___x_2430_;
}
}
else
{
uint8_t v___x_2431_; 
v___x_2431_ = 0;
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef___boxed(lean_object* v_x_2432_){
_start:
{
uint8_t v_res_2433_; lean_object* v_r_2434_; 
v_res_2433_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_x_2432_);
lean_dec_ref(v_x_2432_);
v_r_2434_ = lean_box(v_res_2433_);
return v_r_2434_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(lean_object* v_x_2435_){
_start:
{
if (lean_obj_tag(v_x_2435_) == 4)
{
lean_object* v_declName_2436_; 
v_declName_2436_ = lean_ctor_get(v_x_2435_, 0);
if (lean_obj_tag(v_declName_2436_) == 1)
{
lean_object* v_pre_2437_; 
v_pre_2437_ = lean_ctor_get(v_declName_2436_, 0);
if (lean_obj_tag(v_pre_2437_) == 0)
{
lean_object* v_us_2438_; lean_object* v_str_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v_us_2438_ = lean_ctor_get(v_x_2435_, 1);
v_str_2439_ = lean_ctor_get(v_declName_2436_, 1);
v___x_2440_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2441_ = lean_string_dec_eq(v_str_2439_, v___x_2440_);
if (v___x_2441_ == 0)
{
return v___x_2441_;
}
else
{
if (lean_obj_tag(v_us_2438_) == 0)
{
return v___x_2441_;
}
else
{
uint8_t v___x_2442_; 
v___x_2442_ = 0;
return v___x_2442_;
}
}
}
else
{
uint8_t v___x_2443_; 
v___x_2443_ = 0;
return v___x_2443_;
}
}
else
{
uint8_t v___x_2444_; 
v___x_2444_ = 0;
return v___x_2444_;
}
}
else
{
uint8_t v___x_2445_; 
v___x_2445_ = 0;
return v___x_2445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef___boxed(lean_object* v_x_2446_){
_start:
{
uint8_t v_res_2447_; lean_object* v_r_2448_; 
v_res_2447_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_x_2446_);
lean_dec_ref(v_x_2446_);
v_r_2448_ = lean_box(v_res_2447_);
return v_r_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object* v_x_2449_){
_start:
{
if (lean_obj_tag(v_x_2449_) == 4)
{
lean_object* v_declName_2456_; 
v_declName_2456_ = lean_ctor_get(v_x_2449_, 0);
if (lean_obj_tag(v_declName_2456_) == 1)
{
lean_object* v_pre_2457_; 
v_pre_2457_ = lean_ctor_get(v_declName_2456_, 0);
if (lean_obj_tag(v_pre_2457_) == 0)
{
lean_object* v_us_2458_; lean_object* v_str_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v_us_2458_ = lean_ctor_get(v_x_2449_, 1);
v_str_2459_ = lean_ctor_get(v_declName_2456_, 1);
v___x_2460_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2461_ = lean_string_dec_eq(v_str_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2463_ = lean_string_dec_eq(v_str_2459_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2465_ = lean_string_dec_eq(v_str_2459_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2467_ = lean_string_dec_eq(v_str_2459_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2469_ = lean_string_dec_eq(v_str_2459_, v___x_2468_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2470_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2471_ = lean_string_dec_eq(v_str_2459_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2472_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2473_ = lean_string_dec_eq(v_str_2459_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2475_ = lean_string_dec_eq(v_str_2459_, v___x_2474_);
if (v___x_2475_ == 0)
{
goto v___jp_2450_;
}
else
{
if (lean_obj_tag(v_us_2458_) == 0)
{
goto v___jp_2454_;
}
else
{
goto v___jp_2450_;
}
}
}
else
{
if (lean_obj_tag(v_us_2458_) == 0)
{
goto v___jp_2454_;
}
else
{
goto v___jp_2450_;
}
}
}
else
{
if (lean_obj_tag(v_us_2458_) == 0)
{
goto v___jp_2454_;
}
else
{
goto v___jp_2450_;
}
}
}
else
{
if (lean_obj_tag(v_us_2458_) == 0)
{
goto v___jp_2454_;
}
else
{
goto v___jp_2450_;
}
}
}
else
{
if (lean_obj_tag(v_us_2458_) == 0)
{
goto v___jp_2452_;
}
else
{
goto v___jp_2450_;
}
}
}
else
{
if (lean_obj_tag(v_us_2458_) == 0)
{
goto v___jp_2452_;
}
else
{
goto v___jp_2450_;
}
}
}
else
{
if (lean_obj_tag(v_us_2458_) == 0)
{
goto v___jp_2452_;
}
else
{
goto v___jp_2450_;
}
}
}
else
{
if (lean_obj_tag(v_us_2458_) == 0)
{
goto v___jp_2452_;
}
else
{
goto v___jp_2450_;
}
}
}
else
{
goto v___jp_2450_;
}
}
else
{
goto v___jp_2450_;
}
}
else
{
goto v___jp_2450_;
}
v___jp_2450_:
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2451_;
}
v___jp_2452_:
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2453_;
}
v___jp_2454_:
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed___boxed(lean_object* v_x_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_x_2476_);
lean_dec_ref(v_x_2476_);
return v_res_2477_;
}
}
lean_object* runtime_initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_BorrowedAnnotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_erasedExpr = _init_l_Lean_Compiler_LCNF_erasedExpr();
lean_mark_persistent(l_Lean_Compiler_LCNF_erasedExpr);
l_Lean_Compiler_LCNF_anyExpr = _init_l_Lean_Compiler_LCNF_anyExpr();
lean_mark_persistent(l_Lean_Compiler_LCNF_anyExpr);
l_Lean_Compiler_LCNF_ImpureType_float = _init_l_Lean_Compiler_LCNF_ImpureType_float();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_float);
l_Lean_Compiler_LCNF_ImpureType_float32 = _init_l_Lean_Compiler_LCNF_ImpureType_float32();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_float32);
l_Lean_Compiler_LCNF_ImpureType_uint8 = _init_l_Lean_Compiler_LCNF_ImpureType_uint8();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_uint8);
l_Lean_Compiler_LCNF_ImpureType_uint16 = _init_l_Lean_Compiler_LCNF_ImpureType_uint16();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_uint16);
l_Lean_Compiler_LCNF_ImpureType_uint32 = _init_l_Lean_Compiler_LCNF_ImpureType_uint32();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_uint32);
l_Lean_Compiler_LCNF_ImpureType_uint64 = _init_l_Lean_Compiler_LCNF_ImpureType_uint64();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_uint64);
l_Lean_Compiler_LCNF_ImpureType_usize = _init_l_Lean_Compiler_LCNF_ImpureType_usize();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_usize);
l_Lean_Compiler_LCNF_ImpureType_erased = _init_l_Lean_Compiler_LCNF_ImpureType_erased();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_erased);
l_Lean_Compiler_LCNF_ImpureType_object = _init_l_Lean_Compiler_LCNF_ImpureType_object();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_object);
l_Lean_Compiler_LCNF_ImpureType_tobject = _init_l_Lean_Compiler_LCNF_ImpureType_tobject();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_tobject);
l_Lean_Compiler_LCNF_ImpureType_tagged = _init_l_Lean_Compiler_LCNF_ImpureType_tagged();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_tagged);
l_Lean_Compiler_LCNF_ImpureType_void = _init_l_Lean_Compiler_LCNF_ImpureType_void();
lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_void);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Lean_OriginalConstKind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_BorrowedAnnotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Types(builtin);
}
#ifdef __cplusplus
}
#endif
