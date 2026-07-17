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
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
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
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_getOriginalConstKind_x3f(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0 = (const lean_object*)&l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0_value;
static lean_once_cell_t l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1;
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; 
switch(lean_obj_tag(v_type_207_))
{
case 3:
{
lean_object* v_u_246_; 
v_u_246_ = lean_ctor_get(v_type_207_, 0);
if (lean_obj_tag(v_u_246_) == 0)
{
uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec_ref_known(v_type_207_, 1);
lean_dec_ref(v_xs_208_);
v___x_247_ = 1;
v___x_248_ = lean_box(v___x_247_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
else
{
v___y_219_ = v_a_209_;
v___y_220_ = v_a_210_;
v___y_221_ = v_a_211_;
v___y_222_ = v_a_212_;
goto v___jp_218_;
}
}
case 7:
{
lean_object* v_binderName_250_; lean_object* v_binderType_251_; lean_object* v_body_252_; uint8_t v_binderInfo_253_; lean_object* v___f_254_; lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; 
v_binderName_250_ = lean_ctor_get(v_type_207_, 0);
lean_inc(v_binderName_250_);
v_binderType_251_ = lean_ctor_get(v_type_207_, 1);
lean_inc_ref(v_binderType_251_);
v_body_252_ = lean_ctor_get(v_type_207_, 2);
lean_inc_ref(v_body_252_);
v_binderInfo_253_ = lean_ctor_get_uint8(v_type_207_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_207_, 3);
lean_inc_ref(v_xs_208_);
v___f_254_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_254_, 0, v_xs_208_);
lean_closure_set(v___f_254_, 1, v_body_252_);
v___x_255_ = lean_expr_instantiate_rev(v_binderType_251_, v_xs_208_);
lean_dec_ref(v_xs_208_);
lean_dec_ref(v_binderType_251_);
v___x_256_ = 0;
v___x_257_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_250_, v_binderInfo_253_, v___x_255_, v___f_254_, v___x_256_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
return v___x_257_;
}
default: 
{
v___y_219_ = v_a_209_;
v___y_220_ = v_a_210_;
v___y_221_ = v_a_211_;
v___y_222_ = v_a_212_;
goto v___jp_218_;
}
}
v___jp_214_:
{
uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = 0;
v___x_216_ = lean_box(v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
v___jp_218_:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_expr_instantiate_rev(v_type_207_, v_xs_208_);
lean_dec_ref(v_xs_208_);
lean_dec_ref(v_type_207_);
v___x_224_ = l_Lean_Meta_whnfD(v___x_223_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_237_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_237_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_237_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_237_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
switch(lean_obj_tag(v_a_225_))
{
case 3:
{
lean_object* v_u_229_; 
v_u_229_ = lean_ctor_get(v_a_225_, 0);
lean_inc(v_u_229_);
lean_dec_ref_known(v_a_225_, 1);
if (lean_obj_tag(v_u_229_) == 0)
{
uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = 1;
v___x_231_ = lean_box(v___x_230_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_231_);
v___x_233_ = v___x_227_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
else
{
lean_dec(v_u_229_);
lean_del_object(v___x_227_);
goto v___jp_214_;
}
}
case 7:
{
lean_object* v___x_235_; 
lean_del_object(v___x_227_);
v___x_235_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v_type_207_ = v_a_225_;
v_xs_208_ = v___x_235_;
v_a_209_ = v___y_219_;
v_a_210_ = v___y_220_;
v_a_211_ = v___y_221_;
v_a_212_ = v___y_222_;
goto _start;
}
default: 
{
lean_del_object(v___x_227_);
lean_dec(v_a_225_);
goto v___jp_214_;
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_a_238_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_224_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_224_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(lean_object* v_xs_258_, lean_object* v_body_259_, lean_object* v_x_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_array_push(v_xs_258_, v_x_260_);
v___x_267_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_body_259_, v___x_266_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___boxed(lean_object* v_type_268_, lean_object* v_xs_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_268_, v_xs_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType(lean_object* v_type_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_type_276_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_284_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_276_, v___x_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec_ref(v_type_276_);
v___x_285_ = lean_box(v___x_282_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType___boxed(lean_object* v_type_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Compiler_LCNF_isPropFormerType(v_type_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer(lean_object* v_e_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v___x_300_; 
lean_inc(v_a_298_);
lean_inc_ref(v_a_297_);
lean_inc(v_a_296_);
lean_inc_ref(v_a_295_);
v___x_300_ = lean_infer_type(v_e_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = l_Lean_Compiler_LCNF_isPropFormerType(v_a_301_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
return v___x_302_;
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_300_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_300_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer___boxed(lean_object* v_e_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Compiler_LCNF_isPropFormer(v_e_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(lean_object* v_type_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_keyedConfig_324_; uint8_t v_trackZetaDelta_325_; lean_object* v_zetaDeltaSet_326_; lean_object* v_lctx_327_; lean_object* v_localInstances_328_; lean_object* v_defEqCtx_x3f_329_; lean_object* v_synthPendingDepth_330_; lean_object* v_customCanUnfoldPredicate_x3f_331_; uint8_t v_univApprox_332_; uint8_t v_inTypeClassResolution_333_; uint8_t v_cacheInferType_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_keyedConfig_324_ = lean_ctor_get(v_a_319_, 0);
v_trackZetaDelta_325_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*7);
v_zetaDeltaSet_326_ = lean_ctor_get(v_a_319_, 1);
v_lctx_327_ = lean_ctor_get(v_a_319_, 2);
v_localInstances_328_ = lean_ctor_get(v_a_319_, 3);
v_defEqCtx_x3f_329_ = lean_ctor_get(v_a_319_, 4);
v_synthPendingDepth_330_ = lean_ctor_get(v_a_319_, 5);
v_customCanUnfoldPredicate_x3f_331_ = lean_ctor_get(v_a_319_, 6);
v_univApprox_332_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_333_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*7 + 2);
v_cacheInferType_334_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*7 + 3);
v___x_335_ = 0;
lean_inc_ref(v_keyedConfig_324_);
v___x_336_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_335_, v_keyedConfig_324_);
lean_inc(v_customCanUnfoldPredicate_x3f_331_);
lean_inc(v_synthPendingDepth_330_);
lean_inc(v_defEqCtx_x3f_329_);
lean_inc_ref(v_localInstances_328_);
lean_inc_ref(v_lctx_327_);
lean_inc(v_zetaDeltaSet_326_);
v___x_337_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v_zetaDeltaSet_326_);
lean_ctor_set(v___x_337_, 2, v_lctx_327_);
lean_ctor_set(v___x_337_, 3, v_localInstances_328_);
lean_ctor_set(v___x_337_, 4, v_defEqCtx_x3f_329_);
lean_ctor_set(v___x_337_, 5, v_synthPendingDepth_330_);
lean_ctor_set(v___x_337_, 6, v_customCanUnfoldPredicate_x3f_331_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*7, v_trackZetaDelta_325_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*7 + 1, v_univApprox_332_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*7 + 2, v_inTypeClassResolution_333_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*7 + 3, v_cacheInferType_334_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
v___x_338_ = lean_whnf(v_type_318_, v___x_337_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc_n(v_a_339_, 2);
v___x_340_ = l_Lean_Expr_eta(v_a_339_);
v___x_341_ = lean_expr_eqv(v___x_340_, v_a_339_);
lean_dec(v_a_339_);
if (v___x_341_ == 0)
{
lean_dec_ref_known(v___x_338_, 1);
v_type_318_ = v___x_340_;
goto _start;
}
else
{
lean_dec_ref(v___x_340_);
return v___x_338_;
}
}
else
{
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___boxed(lean_object* v_type_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(lean_object* v_msgData_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; lean_object* v_env_357_; lean_object* v___x_358_; lean_object* v_mctx_359_; lean_object* v_lctx_360_; lean_object* v_options_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_356_ = lean_st_ref_get(v___y_354_);
v_env_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_env_357_);
lean_dec(v___x_356_);
v___x_358_ = lean_st_ref_get(v___y_352_);
v_mctx_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc_ref(v_mctx_359_);
lean_dec(v___x_358_);
v_lctx_360_ = lean_ctor_get(v___y_351_, 2);
v_options_361_ = lean_ctor_get(v___y_353_, 2);
lean_inc_ref(v_options_361_);
lean_inc_ref(v_lctx_360_);
v___x_362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_362_, 0, v_env_357_);
lean_ctor_set(v___x_362_, 1, v_mctx_359_);
lean_ctor_set(v___x_362_, 2, v_lctx_360_);
lean_ctor_set(v___x_362_, 3, v_options_361_);
v___x_363_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v_msgData_350_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6___boxed(lean_object* v_msgData_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msgData_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_ref_378_; lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_388_; 
v_ref_378_ = lean_ctor_get(v___y_375_, 5);
v___x_379_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msg_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_388_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
lean_inc(v_ref_378_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_ref_378_);
lean_ctor_set(v___x_384_, 1, v_a_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 1);
lean_ctor_set(v___x_382_, 0, v___x_384_);
v___x_386_ = v___x_382_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg___boxed(lean_object* v_msg_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(lean_object* v_ref_396_, lean_object* v_msg_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_fileName_403_; lean_object* v_fileMap_404_; lean_object* v_options_405_; lean_object* v_currRecDepth_406_; lean_object* v_maxRecDepth_407_; lean_object* v_ref_408_; lean_object* v_currNamespace_409_; lean_object* v_openDecls_410_; lean_object* v_initHeartbeats_411_; lean_object* v_maxHeartbeats_412_; lean_object* v_quotContext_413_; lean_object* v_currMacroScope_414_; uint8_t v_diag_415_; lean_object* v_cancelTk_x3f_416_; uint8_t v_suppressElabErrors_417_; lean_object* v_inheritedTraceOptions_418_; lean_object* v_ref_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_fileName_403_ = lean_ctor_get(v___y_400_, 0);
v_fileMap_404_ = lean_ctor_get(v___y_400_, 1);
v_options_405_ = lean_ctor_get(v___y_400_, 2);
v_currRecDepth_406_ = lean_ctor_get(v___y_400_, 3);
v_maxRecDepth_407_ = lean_ctor_get(v___y_400_, 4);
v_ref_408_ = lean_ctor_get(v___y_400_, 5);
v_currNamespace_409_ = lean_ctor_get(v___y_400_, 6);
v_openDecls_410_ = lean_ctor_get(v___y_400_, 7);
v_initHeartbeats_411_ = lean_ctor_get(v___y_400_, 8);
v_maxHeartbeats_412_ = lean_ctor_get(v___y_400_, 9);
v_quotContext_413_ = lean_ctor_get(v___y_400_, 10);
v_currMacroScope_414_ = lean_ctor_get(v___y_400_, 11);
v_diag_415_ = lean_ctor_get_uint8(v___y_400_, sizeof(void*)*14);
v_cancelTk_x3f_416_ = lean_ctor_get(v___y_400_, 12);
v_suppressElabErrors_417_ = lean_ctor_get_uint8(v___y_400_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_418_ = lean_ctor_get(v___y_400_, 13);
v_ref_419_ = l_Lean_replaceRef(v_ref_396_, v_ref_408_);
lean_inc_ref(v_inheritedTraceOptions_418_);
lean_inc(v_cancelTk_x3f_416_);
lean_inc(v_currMacroScope_414_);
lean_inc(v_quotContext_413_);
lean_inc(v_maxHeartbeats_412_);
lean_inc(v_initHeartbeats_411_);
lean_inc(v_openDecls_410_);
lean_inc(v_currNamespace_409_);
lean_inc(v_maxRecDepth_407_);
lean_inc(v_currRecDepth_406_);
lean_inc_ref(v_options_405_);
lean_inc_ref(v_fileMap_404_);
lean_inc_ref(v_fileName_403_);
v___x_420_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_420_, 0, v_fileName_403_);
lean_ctor_set(v___x_420_, 1, v_fileMap_404_);
lean_ctor_set(v___x_420_, 2, v_options_405_);
lean_ctor_set(v___x_420_, 3, v_currRecDepth_406_);
lean_ctor_set(v___x_420_, 4, v_maxRecDepth_407_);
lean_ctor_set(v___x_420_, 5, v_ref_419_);
lean_ctor_set(v___x_420_, 6, v_currNamespace_409_);
lean_ctor_set(v___x_420_, 7, v_openDecls_410_);
lean_ctor_set(v___x_420_, 8, v_initHeartbeats_411_);
lean_ctor_set(v___x_420_, 9, v_maxHeartbeats_412_);
lean_ctor_set(v___x_420_, 10, v_quotContext_413_);
lean_ctor_set(v___x_420_, 11, v_currMacroScope_414_);
lean_ctor_set(v___x_420_, 12, v_cancelTk_x3f_416_);
lean_ctor_set(v___x_420_, 13, v_inheritedTraceOptions_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*14, v_diag_415_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*14 + 1, v_suppressElabErrors_417_);
v___x_421_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_397_, v___y_398_, v___y_399_, v___x_420_, v___y_401_);
lean_dec_ref_known(v___x_420_, 14);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg___boxed(lean_object* v_ref_422_, lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_422_, v_msg_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v_ref_422_);
return v_res_429_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_430_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
lean_ctor_set(v___x_435_, 2, v___x_434_);
lean_ctor_set(v___x_435_, 3, v___x_434_);
lean_ctor_set(v___x_435_, 4, v___x_433_);
lean_ctor_set(v___x_435_, 5, v___x_433_);
lean_ctor_set(v___x_435_, 6, v___x_433_);
lean_ctor_set(v___x_435_, 7, v___x_433_);
lean_ctor_set(v___x_435_, 8, v___x_433_);
lean_ctor_set(v___x_435_, 9, v___x_433_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_unsigned_to_nat(32u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_439_ = ((size_t)5ULL);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_unsigned_to_nat(32u);
v___x_442_ = lean_mk_empty_array_with_capacity(v___x_441_);
v___x_443_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_444_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_440_);
lean_ctor_set(v___x_444_, 3, v___x_440_);
lean_ctor_set_usize(v___x_444_, 4, v___x_439_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = lean_box(1);
v___x_446_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_447_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
lean_ctor_set(v___x_448_, 2, v___x_445_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_451_ = l_Lean_stringToMessageData(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_454_ = l_Lean_stringToMessageData(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_470_, lean_object* v_declHint_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; lean_object* v_env_475_; uint8_t v___x_476_; 
v___x_474_ = lean_st_ref_get(v___y_472_);
v_env_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_ref(v_env_475_);
lean_dec(v___x_474_);
v___x_476_ = l_Lean_Name_isAnonymous(v_declHint_471_);
if (v___x_476_ == 0)
{
uint8_t v_isExporting_477_; 
v_isExporting_477_ = lean_ctor_get_uint8(v_env_475_, sizeof(void*)*8);
if (v_isExporting_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec_ref(v_env_475_);
lean_dec(v_declHint_471_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_msg_470_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; uint8_t v___x_480_; 
lean_inc_ref(v_env_475_);
v___x_479_ = l_Lean_Environment_setExporting(v_env_475_, v___x_476_);
lean_inc(v_declHint_471_);
lean_inc_ref(v___x_479_);
v___x_480_ = l_Lean_Environment_contains(v___x_479_, v_declHint_471_, v_isExporting_477_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec_ref(v___x_479_);
lean_dec_ref(v_env_475_);
lean_dec(v_declHint_471_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v_msg_470_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_c_487_; lean_object* v___x_488_; 
v___x_482_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_483_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_484_ = l_Lean_Options_empty;
v___x_485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_485_, 0, v___x_479_);
lean_ctor_set(v___x_485_, 1, v___x_482_);
lean_ctor_set(v___x_485_, 2, v___x_483_);
lean_ctor_set(v___x_485_, 3, v___x_484_);
lean_inc(v_declHint_471_);
v___x_486_ = l_Lean_MessageData_ofConstName(v_declHint_471_, v___x_476_);
v_c_487_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_487_, 0, v___x_485_);
lean_ctor_set(v_c_487_, 1, v___x_486_);
v___x_488_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_475_, v_declHint_471_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec_ref(v_env_475_);
lean_dec(v_declHint_471_);
v___x_489_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_c_487_);
v___x_491_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = l_Lean_MessageData_note(v___x_492_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v_msg_470_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
else
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_531_; 
v_val_496_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_531_ == 0)
{
v___x_498_ = v___x_488_;
v_isShared_499_ = v_isSharedCheck_531_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v___x_488_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_531_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_mod_503_; uint8_t v___x_504_; 
v___x_500_ = lean_box(0);
v___x_501_ = l_Lean_Environment_header(v_env_475_);
lean_dec_ref(v_env_475_);
v___x_502_ = l_Lean_EnvironmentHeader_moduleNames(v___x_501_);
v_mod_503_ = lean_array_get(v___x_500_, v___x_502_, v_val_496_);
lean_dec(v_val_496_);
lean_dec_ref(v___x_502_);
v___x_504_ = l_Lean_isPrivateName(v_declHint_471_);
lean_dec(v_declHint_471_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_505_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v_c_487_);
v___x_507_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_MessageData_ofName(v_mod_503_);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = l_Lean_MessageData_note(v___x_512_);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v_msg_470_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 0);
lean_ctor_set(v___x_498_, 0, v___x_514_);
v___x_516_ = v___x_498_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v_c_487_);
v___x_520_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_MessageData_ofName(v_mod_503_);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_MessageData_note(v___x_525_);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v_msg_470_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 0);
lean_ctor_set(v___x_498_, 0, v___x_527_);
v___x_529_ = v___x_498_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_532_; 
lean_dec_ref(v_env_475_);
lean_dec(v_declHint_471_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v_msg_470_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_533_, lean_object* v_declHint_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_533_, v_declHint_534_, v___y_535_);
lean_dec(v___y_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(lean_object* v_msg_538_, lean_object* v_declHint_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_555_; 
v___x_545_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_538_, v_declHint_539_, v___y_543_);
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_555_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_550_ = l_Lean_unknownIdentifierMessageTag;
v___x_551_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_a_546_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_551_);
v___x_553_ = v___x_548_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9___boxed(lean_object* v_msg_556_, lean_object* v_declHint_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_556_, v_declHint_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(lean_object* v_ref_564_, lean_object* v_msg_565_, lean_object* v_declHint_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v_a_573_; lean_object* v___x_574_; 
v___x_572_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_565_, v_declHint_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref(v___x_572_);
v___x_574_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_564_, v_a_573_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_ref_575_, lean_object* v_msg_576_, lean_object* v_declHint_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_575_, v_msg_576_, v_declHint_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v_ref_575_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(lean_object* v_ref_590_, lean_object* v_constName_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_597_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1);
v___x_598_ = 0;
lean_inc(v_constName_591_);
v___x_599_ = l_Lean_MessageData_ofConstName(v_constName_591_, v___x_598_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_597_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_590_, v___x_602_, v_constName_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___boxed(lean_object* v_ref_604_, lean_object* v_constName_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_604_, v_constName_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v_ref_604_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(lean_object* v_constName_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_ref_618_; lean_object* v___x_619_; 
v_ref_618_ = lean_ctor_get(v___y_615_, 5);
v___x_619_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_618_, v_constName_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg___boxed(lean_object* v_constName_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(lean_object* v_constName_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; lean_object* v_env_634_; uint8_t v___x_635_; lean_object* v___x_636_; 
v___x_633_ = lean_st_ref_get(v___y_631_);
v_env_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_env_634_);
lean_dec(v___x_633_);
v___x_635_ = 0;
lean_inc(v_constName_627_);
v___x_636_ = l_Lean_Environment_find_x3f(v_env_634_, v_constName_627_, v___x_635_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
return v___x_637_;
}
else
{
lean_object* v_val_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_constName_627_);
v_val_638_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_636_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_val_638_);
lean_dec(v___x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 0);
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_val_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4___boxed(lean_object* v_constName_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_constName_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(lean_object* v_binderType_653_, lean_object* v_body_654_, lean_object* v_binderName_655_, uint8_t v_binderInfo_656_, lean_object* v_x_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_binderType_653_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_665_ = lean_expr_instantiate1(v_body_654_, v_x_657_);
v___x_666_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_665_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; uint8_t v___x_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
v___x_668_ = l_Lean_Expr_isErased(v_a_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_680_; 
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v___x_666_, 0);
lean_dec(v_unused_681_);
v___x_670_ = v___x_666_;
v_isShared_671_ = v_isSharedCheck_680_;
goto v_resetjp_669_;
}
else
{
lean_dec(v___x_666_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_680_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_mk_empty_array_with_capacity(v___x_672_);
v___x_674_ = lean_array_push(v___x_673_, v_x_657_);
v___x_675_ = lean_expr_abstract(v_a_667_, v___x_674_);
lean_dec_ref(v___x_674_);
lean_dec(v_a_667_);
v___x_676_ = l_Lean_Expr_lam___override(v_binderName_655_, v_a_664_, v___x_675_, v_binderInfo_656_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_676_);
v___x_678_ = v___x_670_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
else
{
lean_dec(v_a_667_);
lean_dec(v_a_664_);
lean_dec_ref(v_x_657_);
lean_dec(v_binderName_655_);
return v___x_666_;
}
}
else
{
lean_dec(v_a_664_);
lean_dec_ref(v_x_657_);
lean_dec(v_binderName_655_);
return v___x_666_;
}
}
else
{
lean_dec_ref(v_x_657_);
lean_dec(v_binderName_655_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed(lean_object* v_binderType_682_, lean_object* v_body_683_, lean_object* v_binderName_684_, lean_object* v_binderInfo_685_, lean_object* v_x_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v_binderInfo_9702__boxed_692_; lean_object* v_res_693_; 
v_binderInfo_9702__boxed_692_ = lean_unbox(v_binderInfo_685_);
v_res_693_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(v_binderType_682_, v_body_683_, v_binderName_684_, v_binderInfo_9702__boxed_692_, v_x_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v_body_683_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(lean_object* v_d_694_, lean_object* v_xs_695_, lean_object* v_body_696_, lean_object* v_binderName_697_, uint8_t v_binderInfo_698_, lean_object* v_x_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
uint8_t v_isBorrowed_705_; lean_object* v___x_706_; 
v_isBorrowed_705_ = l_Lean_isMarkedBorrowed(v_d_694_);
v___x_706_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_d_694_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v_d_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___x_725_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_725_ = lean_expr_abstract(v_a_707_, v_xs_695_);
lean_dec(v_a_707_);
if (v_isBorrowed_705_ == 0)
{
v_d_709_ = v___x_725_;
v___y_710_ = v___y_700_;
v___y_711_ = v___y_701_;
v___y_712_ = v___y_702_;
v___y_713_ = v___y_703_;
goto v___jp_708_;
}
else
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_markBorrowed(v___x_725_);
v_d_709_ = v___x_726_;
v___y_710_ = v___y_700_;
v___y_711_ = v___y_701_;
v___y_712_ = v___y_702_;
v___y_713_ = v___y_703_;
goto v___jp_708_;
}
v___jp_708_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_array_push(v_xs_695_, v_x_699_);
v___x_715_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_body_696_, v___x_714_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_724_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_724_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = l_Lean_Expr_forallE___override(v_binderName_697_, v_d_709_, v_a_716_, v_binderInfo_698_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_dec_ref(v_d_709_);
lean_dec(v_binderName_697_);
return v___x_715_;
}
}
}
else
{
lean_dec_ref(v_x_699_);
lean_dec(v_binderName_697_);
lean_dec_ref(v_body_696_);
lean_dec_ref(v_xs_695_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed(lean_object* v_d_727_, lean_object* v_xs_728_, lean_object* v_body_729_, lean_object* v_binderName_730_, lean_object* v_binderInfo_731_, lean_object* v_x_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v_binderInfo_9724__boxed_738_; lean_object* v_res_739_; 
v_binderInfo_9724__boxed_738_ = lean_unbox(v_binderInfo_731_);
v_res_739_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(v_d_727_, v_xs_728_, v_body_729_, v_binderName_730_, v_binderInfo_9724__boxed_738_, v_x_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(lean_object* v_e_740_, lean_object* v_xs_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
if (lean_obj_tag(v_e_740_) == 7)
{
lean_object* v_binderName_747_; lean_object* v_binderType_748_; lean_object* v_body_749_; uint8_t v_binderInfo_750_; lean_object* v_d_751_; lean_object* v___x_752_; lean_object* v___f_753_; uint8_t v___x_754_; lean_object* v___x_755_; 
v_binderName_747_ = lean_ctor_get(v_e_740_, 0);
lean_inc_n(v_binderName_747_, 2);
v_binderType_748_ = lean_ctor_get(v_e_740_, 1);
lean_inc_ref(v_binderType_748_);
v_body_749_ = lean_ctor_get(v_e_740_, 2);
lean_inc_ref(v_body_749_);
v_binderInfo_750_ = lean_ctor_get_uint8(v_e_740_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_740_, 3);
v_d_751_ = lean_expr_instantiate_rev(v_binderType_748_, v_xs_741_);
lean_dec_ref(v_binderType_748_);
v___x_752_ = lean_box(v_binderInfo_750_);
lean_inc_ref(v_d_751_);
v___f_753_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed), 11, 5);
lean_closure_set(v___f_753_, 0, v_d_751_);
lean_closure_set(v___f_753_, 1, v_xs_741_);
lean_closure_set(v___f_753_, 2, v_body_749_);
lean_closure_set(v___f_753_, 3, v_binderName_747_);
lean_closure_set(v___f_753_, 4, v___x_752_);
v___x_754_ = 0;
v___x_755_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_747_, v_binderInfo_750_, v_d_751_, v___f_753_, v___x_754_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_expr_instantiate_rev(v_e_740_, v_xs_741_);
lean_dec_ref(v_e_740_);
v___x_757_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_756_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_766_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_766_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_expr_abstract(v_a_758_, v_xs_741_);
lean_dec_ref(v_xs_741_);
lean_dec(v_a_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_762_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
else
{
lean_dec_ref(v_xs_741_);
return v___x_757_;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0(void){
_start:
{
lean_object* v___x_767_; lean_object* v_dummy_768_; 
v___x_767_ = lean_box(0);
v_dummy_768_ = l_Lean_Expr_sort___override(v___x_767_);
return v_dummy_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(lean_object* v_type_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___x_778_; 
lean_inc_ref(v_type_772_);
v___x_778_ = l_Lean_Meta_isProp(v_type_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_845_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_845_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_845_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_845_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
uint8_t v___x_783_; 
v___x_783_ = lean_unbox(v_a_779_);
lean_dec(v_a_779_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
v___x_784_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
switch(lean_obj_tag(v_a_785_))
{
case 3:
{
lean_dec_ref_known(v_a_785_, 1);
lean_del_object(v___x_781_);
return v___x_784_;
}
case 4:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref_known(v___x_784_, 1);
lean_del_object(v___x_781_);
v___x_791_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_792_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_785_, v___x_791_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_792_;
}
case 6:
{
lean_object* v_binderName_793_; lean_object* v_binderType_794_; lean_object* v_body_795_; uint8_t v_binderInfo_796_; lean_object* v___x_797_; lean_object* v___f_798_; uint8_t v___x_799_; lean_object* v___x_800_; 
lean_dec_ref_known(v___x_784_, 1);
lean_del_object(v___x_781_);
v_binderName_793_ = lean_ctor_get(v_a_785_, 0);
lean_inc_n(v_binderName_793_, 2);
v_binderType_794_ = lean_ctor_get(v_a_785_, 1);
lean_inc_ref_n(v_binderType_794_, 2);
v_body_795_ = lean_ctor_get(v_a_785_, 2);
lean_inc_ref(v_body_795_);
v_binderInfo_796_ = lean_ctor_get_uint8(v_a_785_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_785_, 3);
v___x_797_ = lean_box(v_binderInfo_796_);
v___f_798_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_798_, 0, v_binderType_794_);
lean_closure_set(v___f_798_, 1, v_body_795_);
lean_closure_set(v___f_798_, 2, v_binderName_793_);
lean_closure_set(v___f_798_, 3, v___x_797_);
v___x_799_ = 0;
v___x_800_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_793_, v_binderInfo_796_, v_binderType_794_, v___f_798_, v___x_799_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_800_;
}
case 7:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref_known(v___x_784_, 1);
lean_del_object(v___x_781_);
v___x_801_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_802_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_a_785_, v___x_801_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_802_;
}
case 5:
{
lean_object* v_dummy_803_; lean_object* v_nargs_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref_known(v___x_784_, 1);
lean_del_object(v___x_781_);
v_dummy_803_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0);
v_nargs_804_ = l_Lean_Expr_getAppNumArgs(v_a_785_);
lean_inc(v_nargs_804_);
v___x_805_ = lean_mk_array(v_nargs_804_, v_dummy_803_);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_sub(v_nargs_804_, v___x_806_);
lean_dec(v_nargs_804_);
v___x_808_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_a_785_, v___x_805_, v___x_807_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_808_;
}
case 1:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref_known(v___x_784_, 1);
lean_del_object(v___x_781_);
v___x_809_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_810_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_785_, v___x_809_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_810_;
}
case 11:
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_839_; 
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_840_);
v___x_812_ = v___x_784_;
v_isShared_813_ = v_isSharedCheck_839_;
goto v_resetjp_811_;
}
else
{
lean_dec(v___x_784_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_839_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_typeName_814_; 
v_typeName_814_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_typeName_814_);
if (lean_obj_tag(v_typeName_814_) == 1)
{
lean_object* v_pre_815_; 
v_pre_815_ = lean_ctor_get(v_typeName_814_, 0);
if (lean_obj_tag(v_pre_815_) == 0)
{
lean_object* v_idx_816_; lean_object* v_struct_817_; lean_object* v_str_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_idx_816_ = lean_ctor_get(v_a_785_, 1);
lean_inc(v_idx_816_);
v_struct_817_ = lean_ctor_get(v_a_785_, 2);
lean_inc_ref(v_struct_817_);
lean_dec_ref_known(v_a_785_, 3);
v_str_818_ = lean_ctor_get(v_typeName_814_, 1);
lean_inc_ref(v_str_818_);
lean_dec_ref_known(v_typeName_814_, 2);
v___x_819_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1));
v___x_820_ = lean_string_dec_eq(v_str_818_, v___x_819_);
lean_dec_ref(v_str_818_);
if (v___x_820_ == 0)
{
lean_dec_ref(v_struct_817_);
lean_dec(v_idx_816_);
lean_del_object(v___x_812_);
goto v___jp_786_;
}
else
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_nat_dec_eq(v_idx_816_, v___x_821_);
lean_dec(v_idx_816_);
if (v___x_822_ == 0)
{
lean_dec_ref(v_struct_817_);
lean_del_object(v___x_812_);
goto v___jp_786_;
}
else
{
if (lean_obj_tag(v_struct_817_) == 5)
{
lean_object* v_fn_823_; 
v_fn_823_ = lean_ctor_get(v_struct_817_, 0);
lean_inc_ref(v_fn_823_);
lean_dec_ref_known(v_struct_817_, 2);
if (lean_obj_tag(v_fn_823_) == 4)
{
lean_object* v_declName_824_; 
v_declName_824_ = lean_ctor_get(v_fn_823_, 0);
lean_inc(v_declName_824_);
if (lean_obj_tag(v_declName_824_) == 1)
{
lean_object* v_pre_825_; 
v_pre_825_ = lean_ctor_get(v_declName_824_, 0);
lean_inc(v_pre_825_);
if (lean_obj_tag(v_pre_825_) == 1)
{
lean_object* v_pre_826_; 
v_pre_826_ = lean_ctor_get(v_pre_825_, 0);
if (lean_obj_tag(v_pre_826_) == 0)
{
lean_object* v_us_827_; lean_object* v_str_828_; lean_object* v_str_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_us_827_ = lean_ctor_get(v_fn_823_, 1);
lean_inc(v_us_827_);
lean_dec_ref_known(v_fn_823_, 2);
v_str_828_ = lean_ctor_get(v_declName_824_, 1);
lean_inc_ref(v_str_828_);
lean_dec_ref_known(v_declName_824_, 2);
v_str_829_ = lean_ctor_get(v_pre_825_, 1);
lean_inc_ref(v_str_829_);
lean_dec_ref_known(v_pre_825_, 2);
v___x_830_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2));
v___x_831_ = lean_string_dec_eq(v_str_829_, v___x_830_);
lean_dec_ref(v_str_829_);
if (v___x_831_ == 0)
{
lean_dec_ref(v_str_828_);
lean_dec(v_us_827_);
lean_del_object(v___x_812_);
goto v___jp_786_;
}
else
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3));
v___x_833_ = lean_string_dec_eq(v_str_828_, v___x_832_);
lean_dec_ref(v_str_828_);
if (v___x_833_ == 0)
{
lean_dec(v_us_827_);
lean_del_object(v___x_812_);
goto v___jp_786_;
}
else
{
if (lean_obj_tag(v_us_827_) == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
lean_del_object(v___x_781_);
v___x_834_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_835_ = l_Lean_mkConst(v___x_834_, v_us_827_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_835_);
v___x_837_ = v___x_812_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
else
{
lean_dec(v_us_827_);
lean_del_object(v___x_812_);
goto v___jp_786_;
}
}
}
}
else
{
lean_dec_ref_known(v_pre_825_, 2);
lean_dec_ref_known(v_declName_824_, 2);
lean_dec_ref_known(v_fn_823_, 2);
lean_del_object(v___x_812_);
goto v___jp_786_;
}
}
else
{
lean_dec(v_pre_825_);
lean_dec_ref_known(v_declName_824_, 2);
lean_dec_ref_known(v_fn_823_, 2);
lean_del_object(v___x_812_);
goto v___jp_786_;
}
}
else
{
lean_dec(v_declName_824_);
lean_dec_ref_known(v_fn_823_, 2);
lean_del_object(v___x_812_);
goto v___jp_786_;
}
}
else
{
lean_dec_ref(v_fn_823_);
lean_del_object(v___x_812_);
goto v___jp_786_;
}
}
else
{
lean_dec_ref(v_struct_817_);
lean_del_object(v___x_812_);
goto v___jp_786_;
}
}
}
}
else
{
lean_dec_ref_known(v_typeName_814_, 2);
lean_del_object(v___x_812_);
lean_dec_ref_known(v_a_785_, 3);
goto v___jp_786_;
}
}
else
{
lean_dec(v_typeName_814_);
lean_del_object(v___x_812_);
lean_dec_ref_known(v_a_785_, 3);
goto v___jp_786_;
}
}
}
default: 
{
lean_dec_ref_known(v___x_784_, 1);
lean_dec(v_a_785_);
goto v___jp_786_;
}
}
v___jp_786_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_787_);
v___x_789_ = v___x_781_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_del_object(v___x_781_);
return v___x_784_;
}
}
else
{
lean_object* v___x_841_; lean_object* v___x_843_; 
lean_dec_ref(v_type_772_);
v___x_841_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_841_);
v___x_843_ = v___x_781_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v_type_772_);
v_a_846_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_778_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_778_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(lean_object* v_as_854_, size_t v_sz_855_, size_t v_i_856_, lean_object* v_b_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_a_864_; uint8_t v___x_868_; 
v___x_868_ = lean_usize_dec_lt(v_i_856_, v_sz_855_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v_b_857_);
return v___x_869_;
}
else
{
lean_object* v_a_870_; lean_object* v___y_872_; lean_object* v___x_901_; 
v_a_870_ = lean_array_uget_borrowed(v_as_854_, v_i_856_);
lean_inc(v_a_870_);
v___x_901_ = l_Lean_Meta_isProp(v_a_870_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; uint8_t v___x_903_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
v___x_903_ = lean_unbox(v_a_902_);
lean_dec(v_a_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec_ref_known(v___x_901_, 1);
lean_inc(v_a_870_);
v___x_904_ = l_Lean_Compiler_LCNF_isPropFormer(v_a_870_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
v___y_872_ = v___x_904_;
goto v___jp_871_;
}
else
{
v___y_872_ = v___x_901_;
goto v___jp_871_;
}
}
else
{
v___y_872_ = v___x_901_;
goto v___jp_871_;
}
v___jp_871_:
{
if (lean_obj_tag(v___y_872_) == 0)
{
lean_object* v_a_873_; uint8_t v___x_874_; 
v_a_873_ = lean_ctor_get(v___y_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___y_872_, 1);
v___x_874_ = lean_unbox(v_a_873_);
lean_dec(v_a_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; 
lean_inc(v_a_870_);
v___x_875_ = l_Lean_Meta_isTypeFormer(v_a_870_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; uint8_t v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
v___x_877_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_879_ = l_Lean_Expr_app___override(v_b_857_, v___x_878_);
v_a_864_ = v___x_879_;
goto v___jp_863_;
}
else
{
lean_object* v___x_880_; 
lean_inc(v_a_870_);
v___x_880_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_a_870_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = l_Lean_Expr_app___override(v_b_857_, v_a_881_);
v_a_864_ = v___x_882_;
goto v___jp_863_;
}
else
{
lean_dec_ref(v_b_857_);
return v___x_880_;
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v_b_857_);
v_a_883_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_875_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_875_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_892_ = l_Lean_Expr_app___override(v_b_857_, v___x_891_);
v_a_864_ = v___x_892_;
goto v___jp_863_;
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v_b_857_);
v_a_893_ = lean_ctor_get(v___y_872_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___y_872_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___y_872_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___y_872_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
v___jp_863_:
{
size_t v___x_865_; size_t v___x_866_; 
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_add(v_i_856_, v___x_865_);
v_i_856_ = v___x_866_;
v_b_857_ = v_a_864_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(lean_object* v_f_908_, lean_object* v_args_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_fNew_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; 
switch(lean_obj_tag(v_f_908_))
{
case 4:
{
lean_object* v_declName_924_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___x_948_; lean_object* v_env_949_; uint8_t v_isExporting_950_; 
v_declName_924_ = lean_ctor_get(v_f_908_, 0);
v___x_948_ = lean_st_ref_get(v_a_913_);
v_env_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc_ref(v_env_949_);
lean_dec(v___x_948_);
v_isExporting_950_ = lean_ctor_get_uint8(v_env_949_, sizeof(void*)*8);
lean_dec_ref(v_env_949_);
if (v_isExporting_950_ == 0)
{
v___y_926_ = v_a_910_;
v___y_927_ = v_a_911_;
v___y_928_ = v_a_912_;
v___y_929_ = v_a_913_;
goto v___jp_925_;
}
else
{
uint8_t v___x_951_; 
v___x_951_ = l_Lean_isPrivateName(v_declName_924_);
if (v___x_951_ == 0)
{
v___y_926_ = v_a_910_;
v___y_927_ = v_a_911_;
v___y_928_ = v_a_912_;
v___y_929_ = v_a_913_;
goto v___jp_925_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1);
v___x_953_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_952_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_dec_ref_known(v___x_953_, 1);
v___y_926_ = v_a_910_;
v___y_927_ = v_a_911_;
v___y_928_ = v_a_912_;
v___y_929_ = v_a_913_;
goto v___jp_925_;
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref_known(v_f_908_, 2);
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
v___jp_925_:
{
lean_object* v___x_930_; 
lean_inc(v_declName_924_);
v___x_930_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_declName_924_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_939_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
if (lean_obj_tag(v_a_931_) == 5)
{
lean_dec_ref_known(v_a_931_, 1);
lean_del_object(v___x_933_);
v_fNew_916_ = v_f_908_;
v___y_917_ = v___y_926_;
v___y_918_ = v___y_927_;
v___y_919_ = v___y_928_;
v___y_920_ = v___y_929_;
goto v___jp_915_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_937_; 
lean_dec(v_a_931_);
lean_dec_ref_known(v_f_908_, 2);
v___x_935_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref_known(v_f_908_, 2);
v_a_940_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_930_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_930_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
case 1:
{
v_fNew_916_ = v_f_908_;
v___y_917_ = v_a_910_;
v___y_918_ = v_a_911_;
v___y_919_ = v_a_912_;
v___y_920_ = v_a_913_;
goto v___jp_915_;
}
default: 
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec_ref(v_f_908_);
v___x_962_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
v___jp_915_:
{
size_t v_sz_921_; size_t v___x_922_; lean_object* v___x_923_; 
v_sz_921_ = lean_array_size(v_args_909_);
v___x_922_ = ((size_t)0ULL);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_args_909_, v_sz_921_, v___x_922_, v_fNew_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
if (lean_obj_tag(v_x_964_) == 5)
{
lean_object* v_fn_972_; lean_object* v_arg_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_fn_972_ = lean_ctor_get(v_x_964_, 0);
lean_inc_ref(v_fn_972_);
v_arg_973_ = lean_ctor_get(v_x_964_, 1);
lean_inc_ref(v_arg_973_);
lean_dec_ref_known(v_x_964_, 2);
v___x_974_ = lean_array_set(v_x_965_, v_x_966_, v_arg_973_);
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_nat_sub(v_x_966_, v___x_975_);
lean_dec(v_x_966_);
v_x_964_ = v_fn_972_;
v_x_965_ = v___x_974_;
v_x_966_ = v___x_976_;
goto _start;
}
else
{
lean_object* v___x_978_; 
lean_dec(v_x_966_);
v___x_978_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_x_964_, v_x_965_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec_ref(v_x_965_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0___boxed(lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_x_979_, v_x_980_, v_x_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___boxed(lean_object* v_e_988_, lean_object* v_xs_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_e_988_, v_xs_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___boxed(lean_object* v_f_996_, lean_object* v_args_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_f_996_, v_args_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec_ref(v_args_997_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3___boxed(lean_object* v_as_1004_, lean_object* v_sz_1005_, lean_object* v_i_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
size_t v_sz_boxed_1013_; size_t v_i_boxed_1014_; lean_object* v_res_1015_; 
v_sz_boxed_1013_ = lean_unbox_usize(v_sz_1005_);
lean_dec(v_sz_1005_);
v_i_boxed_1014_ = lean_unbox_usize(v_i_1006_);
lean_dec(v_i_1006_);
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_as_1004_, v_sz_boxed_1013_, v_i_boxed_1014_, v_b_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec_ref(v_as_1004_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed(lean_object* v_type_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(lean_object* v_00_u03b1_1023_, lean_object* v_msg_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___boxed(lean_object* v_00_u03b1_1031_, lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(v_00_u03b1_1031_, v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(lean_object* v_00_u03b1_1039_, lean_object* v_constName_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_constName_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(v_00_u03b1_1047_, v_constName_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(lean_object* v_00_u03b1_1055_, lean_object* v_ref_1056_, lean_object* v_constName_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_1056_, v_constName_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_ref_1065_, lean_object* v_constName_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(v_00_u03b1_1064_, v_ref_1065_, v_constName_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v_ref_1065_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(lean_object* v_00_u03b1_1073_, lean_object* v_ref_1074_, lean_object* v_msg_1075_, lean_object* v_declHint_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_1074_, v_msg_1075_, v_declHint_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1083_, lean_object* v_ref_1084_, lean_object* v_msg_1085_, lean_object* v_declHint_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(v_00_u03b1_1083_, v_ref_1084_, v_msg_1085_, v_declHint_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v_ref_1084_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(lean_object* v_msg_1093_, lean_object* v_declHint_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1093_, v_declHint_1094_, v___y_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_1101_, lean_object* v_declHint_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(v_msg_1101_, v_declHint_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(lean_object* v_00_u03b1_1109_, lean_object* v_ref_1110_, lean_object* v_msg_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1110_, v_msg_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_ref_1119_, lean_object* v_msg_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(v_00_u03b1_1118_, v_ref_1119_, v_msg_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v_ref_1119_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(lean_object* v___y_1127_, uint8_t v_isExporting_1128_, lean_object* v___x_1129_, lean_object* v___y_1130_, lean_object* v___x_1131_, lean_object* v_a_x3f_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v_env_1135_; lean_object* v_nextMacroScope_1136_; lean_object* v_ngen_1137_; lean_object* v_auxDeclNGen_1138_; lean_object* v_traceState_1139_; lean_object* v_messages_1140_; lean_object* v_infoState_1141_; lean_object* v_snapshotTasks_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1167_; 
v___x_1134_ = lean_st_ref_take(v___y_1127_);
v_env_1135_ = lean_ctor_get(v___x_1134_, 0);
v_nextMacroScope_1136_ = lean_ctor_get(v___x_1134_, 1);
v_ngen_1137_ = lean_ctor_get(v___x_1134_, 2);
v_auxDeclNGen_1138_ = lean_ctor_get(v___x_1134_, 3);
v_traceState_1139_ = lean_ctor_get(v___x_1134_, 4);
v_messages_1140_ = lean_ctor_get(v___x_1134_, 6);
v_infoState_1141_ = lean_ctor_get(v___x_1134_, 7);
v_snapshotTasks_1142_ = lean_ctor_get(v___x_1134_, 8);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; 
v_unused_1168_ = lean_ctor_get(v___x_1134_, 5);
lean_dec(v_unused_1168_);
v___x_1144_ = v___x_1134_;
v_isShared_1145_ = v_isSharedCheck_1167_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_snapshotTasks_1142_);
lean_inc(v_infoState_1141_);
lean_inc(v_messages_1140_);
lean_inc(v_traceState_1139_);
lean_inc(v_auxDeclNGen_1138_);
lean_inc(v_ngen_1137_);
lean_inc(v_nextMacroScope_1136_);
lean_inc(v_env_1135_);
lean_dec(v___x_1134_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1167_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = l_Lean_Environment_setExporting(v_env_1135_, v_isExporting_1128_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 5, v___x_1129_);
lean_ctor_set(v___x_1144_, 0, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_nextMacroScope_1136_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_ngen_1137_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_auxDeclNGen_1138_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_traceState_1139_);
lean_ctor_set(v_reuseFailAlloc_1166_, 5, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1166_, 6, v_messages_1140_);
lean_ctor_set(v_reuseFailAlloc_1166_, 7, v_infoState_1141_);
lean_ctor_set(v_reuseFailAlloc_1166_, 8, v_snapshotTasks_1142_);
v___x_1148_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_mctx_1151_; lean_object* v_zetaDeltaFVarIds_1152_; lean_object* v_postponed_1153_; lean_object* v_diag_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1164_; 
v___x_1149_ = lean_st_ref_set(v___y_1127_, v___x_1148_);
v___x_1150_ = lean_st_ref_take(v___y_1130_);
v_mctx_1151_ = lean_ctor_get(v___x_1150_, 0);
v_zetaDeltaFVarIds_1152_ = lean_ctor_get(v___x_1150_, 2);
v_postponed_1153_ = lean_ctor_get(v___x_1150_, 3);
v_diag_1154_ = lean_ctor_get(v___x_1150_, 4);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v___x_1150_, 1);
lean_dec(v_unused_1165_);
v___x_1156_ = v___x_1150_;
v_isShared_1157_ = v_isSharedCheck_1164_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_diag_1154_);
lean_inc(v_postponed_1153_);
lean_inc(v_zetaDeltaFVarIds_1152_);
lean_inc(v_mctx_1151_);
lean_dec(v___x_1150_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1164_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v___x_1131_);
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_mctx_1151_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_zetaDeltaFVarIds_1152_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v_postponed_1153_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v_diag_1154_);
v___x_1159_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = lean_st_ref_set(v___y_1130_, v___x_1159_);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0___boxed(lean_object* v___y_1169_, lean_object* v_isExporting_1170_, lean_object* v___x_1171_, lean_object* v___y_1172_, lean_object* v___x_1173_, lean_object* v_a_x3f_1174_, lean_object* v___y_1175_){
_start:
{
uint8_t v_isExporting_boxed_1176_; lean_object* v_res_1177_; 
v_isExporting_boxed_1176_ = lean_unbox(v_isExporting_1170_);
v_res_1177_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1169_, v_isExporting_boxed_1176_, v___x_1171_, v___y_1172_, v___x_1173_, v_a_x3f_1174_);
lean_dec(v_a_x3f_1174_);
lean_dec(v___y_1172_);
lean_dec(v___y_1169_);
return v_res_1177_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
v___x_1184_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_ctor_set(v___x_1184_, 2, v___x_1183_);
lean_ctor_set(v___x_1184_, 3, v___x_1183_);
lean_ctor_set(v___x_1184_, 4, v___x_1183_);
lean_ctor_set(v___x_1184_, 5, v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(lean_object* v_x_1185_, uint8_t v_isExporting_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_env_1193_; uint8_t v_isExporting_1194_; lean_object* v___x_1260_; uint8_t v_isModule_1261_; 
v___x_1192_ = lean_st_ref_get(v___y_1190_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_env_1193_);
lean_dec(v___x_1192_);
v_isExporting_1194_ = lean_ctor_get_uint8(v_env_1193_, sizeof(void*)*8);
v___x_1260_ = l_Lean_Environment_header(v_env_1193_);
lean_dec_ref(v_env_1193_);
v_isModule_1261_ = lean_ctor_get_uint8(v___x_1260_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1260_);
if (v_isModule_1261_ == 0)
{
lean_object* v___x_1262_; 
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
v___x_1262_ = lean_apply_5(v_x_1185_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
return v___x_1262_;
}
else
{
if (v_isExporting_1194_ == 0)
{
if (v_isExporting_1186_ == 0)
{
lean_object* v___x_1263_; 
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
v___x_1263_ = lean_apply_5(v_x_1185_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
return v___x_1263_;
}
else
{
goto v___jp_1195_;
}
}
else
{
if (v_isExporting_1186_ == 0)
{
goto v___jp_1195_;
}
else
{
lean_object* v___x_1264_; 
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
v___x_1264_ = lean_apply_5(v_x_1185_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
return v___x_1264_;
}
}
}
v___jp_1195_:
{
lean_object* v___x_1196_; lean_object* v_env_1197_; lean_object* v_nextMacroScope_1198_; lean_object* v_ngen_1199_; lean_object* v_auxDeclNGen_1200_; lean_object* v_traceState_1201_; lean_object* v_messages_1202_; lean_object* v_infoState_1203_; lean_object* v_snapshotTasks_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1258_; 
v___x_1196_ = lean_st_ref_take(v___y_1190_);
v_env_1197_ = lean_ctor_get(v___x_1196_, 0);
v_nextMacroScope_1198_ = lean_ctor_get(v___x_1196_, 1);
v_ngen_1199_ = lean_ctor_get(v___x_1196_, 2);
v_auxDeclNGen_1200_ = lean_ctor_get(v___x_1196_, 3);
v_traceState_1201_ = lean_ctor_get(v___x_1196_, 4);
v_messages_1202_ = lean_ctor_get(v___x_1196_, 6);
v_infoState_1203_ = lean_ctor_get(v___x_1196_, 7);
v_snapshotTasks_1204_ = lean_ctor_get(v___x_1196_, 8);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1196_, 5);
lean_dec(v_unused_1259_);
v___x_1206_ = v___x_1196_;
v_isShared_1207_ = v_isSharedCheck_1258_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_snapshotTasks_1204_);
lean_inc(v_infoState_1203_);
lean_inc(v_messages_1202_);
lean_inc(v_traceState_1201_);
lean_inc(v_auxDeclNGen_1200_);
lean_inc(v_ngen_1199_);
lean_inc(v_nextMacroScope_1198_);
lean_inc(v_env_1197_);
lean_dec(v___x_1196_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1258_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1208_ = l_Lean_Environment_setExporting(v_env_1197_, v_isExporting_1186_);
v___x_1209_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 5, v___x_1209_);
lean_ctor_set(v___x_1206_, 0, v___x_1208_);
v___x_1211_ = v___x_1206_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_nextMacroScope_1198_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_ngen_1199_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_auxDeclNGen_1200_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_traceState_1201_);
lean_ctor_set(v_reuseFailAlloc_1257_, 5, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1257_, 6, v_messages_1202_);
lean_ctor_set(v_reuseFailAlloc_1257_, 7, v_infoState_1203_);
lean_ctor_set(v_reuseFailAlloc_1257_, 8, v_snapshotTasks_1204_);
v___x_1211_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_mctx_1214_; lean_object* v_zetaDeltaFVarIds_1215_; lean_object* v_postponed_1216_; lean_object* v_diag_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1255_; 
v___x_1212_ = lean_st_ref_set(v___y_1190_, v___x_1211_);
v___x_1213_ = lean_st_ref_take(v___y_1188_);
v_mctx_1214_ = lean_ctor_get(v___x_1213_, 0);
v_zetaDeltaFVarIds_1215_ = lean_ctor_get(v___x_1213_, 2);
v_postponed_1216_ = lean_ctor_get(v___x_1213_, 3);
v_diag_1217_ = lean_ctor_get(v___x_1213_, 4);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___x_1213_, 1);
lean_dec(v_unused_1256_);
v___x_1219_ = v___x_1213_;
v_isShared_1220_ = v_isSharedCheck_1255_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_diag_1217_);
lean_inc(v_postponed_1216_);
lean_inc(v_zetaDeltaFVarIds_1215_);
lean_inc(v_mctx_1214_);
lean_dec(v___x_1213_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1255_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___x_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_mctx_1214_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_zetaDeltaFVarIds_1215_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_postponed_1216_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_diag_1217_);
v___x_1223_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v_r_1225_; 
v___x_1224_ = lean_st_ref_set(v___y_1188_, v___x_1223_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
v_r_1225_ = lean_apply_5(v_x_1185_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
if (lean_obj_tag(v_r_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1242_; 
v_a_1226_ = lean_ctor_get(v_r_1225_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_r_1225_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1228_ = v_r_1225_;
v_isShared_1229_ = v_isSharedCheck_1242_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v_r_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1242_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
lean_inc(v_a_1226_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set_tag(v___x_1228_, 1);
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
v___x_1232_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1190_, v_isExporting_1194_, v___x_1209_, v___y_1188_, v___x_1221_, v___x_1231_);
lean_dec_ref(v___x_1231_);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v___x_1232_, 0);
lean_dec(v_unused_1240_);
v___x_1234_ = v___x_1232_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_dec(v___x_1232_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v_a_1226_);
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1226_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_a_1243_ = lean_ctor_get(v_r_1225_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v_r_1225_, 1);
v___x_1244_ = lean_box(0);
v___x_1245_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1190_, v_isExporting_1194_, v___x_1209_, v___y_1188_, v___x_1221_, v___x_1244_);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___x_1245_, 0);
lean_dec(v_unused_1253_);
v___x_1247_ = v___x_1245_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_dec(v___x_1245_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 1);
lean_ctor_set(v___x_1247_, 0, v_a_1243_);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1243_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___boxed(lean_object* v_x_1265_, lean_object* v_isExporting_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v_isExporting_boxed_1272_; lean_object* v_res_1273_; 
v_isExporting_boxed_1272_ = lean_unbox(v_isExporting_1266_);
v_res_1273_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1265_, v_isExporting_boxed_1272_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object* v_00_u03b1_1274_, lean_object* v_x_1275_, uint8_t v_isExporting_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1275_, v_isExporting_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_x_1284_, lean_object* v_isExporting_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
uint8_t v_isExporting_boxed_1291_; lean_object* v_res_1292_; 
v_isExporting_boxed_1291_ = lean_unbox(v_isExporting_1285_);
v_res_1292_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(v_00_u03b1_1283_, v_x_1284_, v_isExporting_boxed_1291_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
return v_res_1292_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(lean_object* v_opts_1293_, lean_object* v_opt_1294_){
_start:
{
lean_object* v_name_1295_; lean_object* v_defValue_1296_; lean_object* v_map_1297_; lean_object* v___x_1298_; 
v_name_1295_ = lean_ctor_get(v_opt_1294_, 0);
v_defValue_1296_ = lean_ctor_get(v_opt_1294_, 1);
v_map_1297_ = lean_ctor_get(v_opts_1293_, 0);
v___x_1298_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1297_, v_name_1295_);
if (lean_obj_tag(v___x_1298_) == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_unbox(v_defValue_1296_);
return v___x_1299_;
}
else
{
lean_object* v_val_1300_; 
v_val_1300_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1300_);
lean_dec_ref_known(v___x_1298_, 1);
if (lean_obj_tag(v_val_1300_) == 1)
{
uint8_t v_v_1301_; 
v_v_1301_ = lean_ctor_get_uint8(v_val_1300_, 0);
lean_dec_ref_known(v_val_1300_, 0);
return v_v_1301_;
}
else
{
uint8_t v___x_1302_; 
lean_dec(v_val_1300_);
v___x_1302_ = lean_unbox(v_defValue_1296_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5___boxed(lean_object* v_opts_1303_, lean_object* v_opt_1304_){
_start:
{
uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_res_1305_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v_opts_1303_, v_opt_1304_);
lean_dec_ref(v_opt_1304_);
lean_dec_ref(v_opts_1303_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(lean_object* v_opts_1307_, lean_object* v_opt_1308_){
_start:
{
lean_object* v_name_1309_; lean_object* v_defValue_1310_; lean_object* v_map_1311_; lean_object* v___x_1312_; 
v_name_1309_ = lean_ctor_get(v_opt_1308_, 0);
v_defValue_1310_ = lean_ctor_get(v_opt_1308_, 1);
v_map_1311_ = lean_ctor_get(v_opts_1307_, 0);
v___x_1312_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1311_, v_name_1309_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_inc(v_defValue_1310_);
return v_defValue_1310_;
}
else
{
lean_object* v_val_1313_; 
v_val_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v___x_1312_, 1);
if (lean_obj_tag(v_val_1313_) == 3)
{
lean_object* v_v_1314_; 
v_v_1314_ = lean_ctor_get(v_val_1313_, 0);
lean_inc(v_v_1314_);
lean_dec_ref_known(v_val_1313_, 1);
return v_v_1314_;
}
else
{
lean_dec(v_val_1313_);
lean_inc(v_defValue_1310_);
return v_defValue_1310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6___boxed(lean_object* v_opts_1315_, lean_object* v_opt_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(v_opts_1315_, v_opt_1316_);
lean_dec_ref(v_opt_1316_);
lean_dec_ref(v_opts_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object* v_a_1318_, lean_object* v_diag_1319_, lean_object* v_a_x3f_1320_){
_start:
{
lean_object* v___x_1322_; lean_object* v_mctx_1323_; lean_object* v_cache_1324_; lean_object* v_zetaDeltaFVarIds_1325_; lean_object* v_postponed_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1336_; 
v___x_1322_ = lean_st_ref_take(v_a_1318_);
v_mctx_1323_ = lean_ctor_get(v___x_1322_, 0);
v_cache_1324_ = lean_ctor_get(v___x_1322_, 1);
v_zetaDeltaFVarIds_1325_ = lean_ctor_get(v___x_1322_, 2);
v_postponed_1326_ = lean_ctor_get(v___x_1322_, 3);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v___x_1322_, 4);
lean_dec(v_unused_1337_);
v___x_1328_ = v___x_1322_;
v_isShared_1329_ = v_isSharedCheck_1336_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_postponed_1326_);
lean_inc(v_zetaDeltaFVarIds_1325_);
lean_inc(v_cache_1324_);
lean_inc(v_mctx_1323_);
lean_dec(v___x_1322_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1336_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 4, v_diag_1319_);
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_mctx_1323_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_cache_1324_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_zetaDeltaFVarIds_1325_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v_postponed_1326_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v_diag_1319_);
v___x_1331_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = lean_st_ref_set(v_a_1318_, v___x_1331_);
v___x_1333_ = lean_box(0);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object* v_a_1338_, lean_object* v_diag_1339_, lean_object* v_a_x3f_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1338_, v_diag_1339_, v_a_x3f_1340_);
lean_dec(v_a_x3f_1340_);
lean_dec(v_a_1338_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0(lean_object* v_ps_1343_, lean_object* v_k_1344_, lean_object* v_v_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_k_1344_);
lean_ctor_set(v___x_1346_, 1, v_v_1345_);
v___x_1347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v_ps_1343_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(lean_object* v_f_1348_, lean_object* v_keys_1349_, lean_object* v_vals_1350_, lean_object* v_i_1351_, lean_object* v_acc_1352_){
_start:
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = lean_array_get_size(v_keys_1349_);
v___x_1354_ = lean_nat_dec_lt(v_i_1351_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_dec(v_i_1351_);
lean_dec(v_f_1348_);
return v_acc_1352_;
}
else
{
lean_object* v_k_1355_; lean_object* v_v_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v_k_1355_ = lean_array_fget_borrowed(v_keys_1349_, v_i_1351_);
v_v_1356_ = lean_array_fget_borrowed(v_vals_1350_, v_i_1351_);
lean_inc(v_f_1348_);
lean_inc(v_v_1356_);
lean_inc(v_k_1355_);
v___x_1357_ = lean_apply_3(v_f_1348_, v_acc_1352_, v_k_1355_, v_v_1356_);
v___x_1358_ = lean_unsigned_to_nat(1u);
v___x_1359_ = lean_nat_add(v_i_1351_, v___x_1358_);
lean_dec(v_i_1351_);
v_i_1351_ = v___x_1359_;
v_acc_1352_ = v___x_1357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_f_1361_, lean_object* v_keys_1362_, lean_object* v_vals_1363_, lean_object* v_i_1364_, lean_object* v_acc_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1361_, v_keys_1362_, v_vals_1363_, v_i_1364_, v_acc_1365_);
lean_dec_ref(v_vals_1363_);
lean_dec_ref(v_keys_1362_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(lean_object* v_f_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
if (lean_obj_tag(v_x_1368_) == 0)
{
lean_object* v_es_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_es_1370_ = lean_ctor_get(v_x_1368_, 0);
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = lean_array_get_size(v_es_1370_);
v___x_1373_ = lean_nat_dec_lt(v___x_1371_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_dec(v_f_1367_);
return v_x_1369_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_nat_dec_le(v___x_1372_, v___x_1372_);
if (v___x_1374_ == 0)
{
if (v___x_1373_ == 0)
{
lean_dec(v_f_1367_);
return v_x_1369_;
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = lean_usize_of_nat(v___x_1372_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1367_, v_es_1370_, v___x_1375_, v___x_1376_, v_x_1369_);
return v___x_1377_;
}
}
else
{
size_t v___x_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = ((size_t)0ULL);
v___x_1379_ = lean_usize_of_nat(v___x_1372_);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1367_, v_es_1370_, v___x_1378_, v___x_1379_, v_x_1369_);
return v___x_1380_;
}
}
}
else
{
lean_object* v_ks_1381_; lean_object* v_vs_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_ks_1381_ = lean_ctor_get(v_x_1368_, 0);
v_vs_1382_ = lean_ctor_get(v_x_1368_, 1);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1367_, v_ks_1381_, v_vs_1382_, v___x_1383_, v_x_1369_);
return v___x_1384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(lean_object* v_f_1385_, lean_object* v_as_1386_, size_t v_i_1387_, size_t v_stop_1388_, lean_object* v_b_1389_){
_start:
{
lean_object* v___y_1391_; uint8_t v___x_1395_; 
v___x_1395_ = lean_usize_dec_eq(v_i_1387_, v_stop_1388_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_array_uget_borrowed(v_as_1386_, v_i_1387_);
switch(lean_obj_tag(v___x_1396_))
{
case 0:
{
lean_object* v_key_1397_; lean_object* v_val_1398_; lean_object* v___x_1399_; 
v_key_1397_ = lean_ctor_get(v___x_1396_, 0);
v_val_1398_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_f_1385_);
lean_inc(v_val_1398_);
lean_inc(v_key_1397_);
v___x_1399_ = lean_apply_3(v_f_1385_, v_b_1389_, v_key_1397_, v_val_1398_);
v___y_1391_ = v___x_1399_;
goto v___jp_1390_;
}
case 1:
{
lean_object* v_node_1400_; lean_object* v___x_1401_; 
v_node_1400_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_f_1385_);
v___x_1401_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1385_, v_node_1400_, v_b_1389_);
v___y_1391_ = v___x_1401_;
goto v___jp_1390_;
}
default: 
{
v___y_1391_ = v_b_1389_;
goto v___jp_1390_;
}
}
}
else
{
lean_dec(v_f_1385_);
return v_b_1389_;
}
v___jp_1390_:
{
size_t v___x_1392_; size_t v___x_1393_; 
v___x_1392_ = ((size_t)1ULL);
v___x_1393_ = lean_usize_add(v_i_1387_, v___x_1392_);
v_i_1387_ = v___x_1393_;
v_b_1389_ = v___y_1391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg___boxed(lean_object* v_f_1402_, lean_object* v_as_1403_, lean_object* v_i_1404_, lean_object* v_stop_1405_, lean_object* v_b_1406_){
_start:
{
size_t v_i_boxed_1407_; size_t v_stop_boxed_1408_; lean_object* v_res_1409_; 
v_i_boxed_1407_ = lean_unbox_usize(v_i_1404_);
lean_dec(v_i_1404_);
v_stop_boxed_1408_ = lean_unbox_usize(v_stop_1405_);
lean_dec(v_stop_1405_);
v_res_1409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1402_, v_as_1403_, v_i_boxed_1407_, v_stop_boxed_1408_, v_b_1406_);
lean_dec_ref(v_as_1403_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_f_1410_, lean_object* v_x_1411_, lean_object* v_x_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1410_, v_x_1411_, v_x_1412_);
lean_dec_ref(v_x_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0(lean_object* v_f_1414_, lean_object* v_x1_1415_, lean_object* v_x2_1416_, lean_object* v_x3_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_apply_3(v_f_1414_, v_x1_1415_, v_x2_1416_, v_x3_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(lean_object* v_map_1419_, lean_object* v_f_1420_, lean_object* v_init_1421_){
_start:
{
lean_object* v___f_1422_; lean_object* v___x_1423_; 
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1422_, 0, v_f_1420_);
v___x_1423_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v___f_1422_, v_map_1419_, v_init_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___boxed(lean_object* v_map_1424_, lean_object* v_f_1425_, lean_object* v_init_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_1424_, v_f_1425_, v_init_1426_);
lean_dec_ref(v_map_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(lean_object* v_m_1429_){
_start:
{
lean_object* v___f_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___f_1430_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0));
v___x_1431_ = lean_box(0);
v___x_1432_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_m_1429_, v___f_1430_, v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___boxed(lean_object* v_m_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1433_);
lean_dec_ref(v_m_1433_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(lean_object* v_o_1438_, lean_object* v_k_1439_, uint8_t v_v_1440_){
_start:
{
lean_object* v_map_1441_; uint8_t v_hasTrace_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1456_; 
v_map_1441_ = lean_ctor_get(v_o_1438_, 0);
v_hasTrace_1442_ = lean_ctor_get_uint8(v_o_1438_, sizeof(void*)*1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_o_1438_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1444_ = v_o_1438_;
v_isShared_1445_ = v_isSharedCheck_1456_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_map_1441_);
lean_dec(v_o_1438_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1456_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1446_, 0, v_v_1440_);
lean_inc(v_k_1439_);
v___x_1447_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1439_, v___x_1446_, v_map_1441_);
if (v_hasTrace_1442_ == 0)
{
lean_object* v___x_1448_; uint8_t v___x_1449_; lean_object* v___x_1451_; 
v___x_1448_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1));
v___x_1449_ = l_Lean_Name_isPrefixOf(v___x_1448_, v_k_1439_);
lean_dec(v_k_1439_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1447_);
v___x_1451_ = v___x_1444_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1447_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*1, v___x_1449_);
return v___x_1451_;
}
}
else
{
lean_object* v___x_1454_; 
lean_dec(v_k_1439_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1447_);
v___x_1454_ = v___x_1444_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1447_);
lean_ctor_set_uint8(v_reuseFailAlloc_1455_, sizeof(void*)*1, v_hasTrace_1442_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___boxed(lean_object* v_o_1457_, lean_object* v_k_1458_, lean_object* v_v_1459_){
_start:
{
uint8_t v_v_boxed_1460_; lean_object* v_res_1461_; 
v_v_boxed_1460_ = lean_unbox(v_v_1459_);
v_res_1461_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(v_o_1457_, v_k_1458_, v_v_boxed_1460_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(lean_object* v_opts_1462_, lean_object* v_opt_1463_, uint8_t v_val_1464_){
_start:
{
lean_object* v_name_1465_; lean_object* v___x_1466_; 
v_name_1465_ = lean_ctor_get(v_opt_1463_, 0);
lean_inc(v_name_1465_);
lean_dec_ref(v_opt_1463_);
v___x_1466_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(v_opts_1462_, v_name_1465_, v_val_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4___boxed(lean_object* v_opts_1467_, lean_object* v_opt_1468_, lean_object* v_val_1469_){
_start:
{
uint8_t v_val_boxed_1470_; lean_object* v_res_1471_; 
v_val_boxed_1470_ = lean_unbox(v_val_1469_);
v_res_1471_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v_opts_1467_, v_opt_1468_, v_val_boxed_1470_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(lean_object* v_keys_1472_, lean_object* v_vals_1473_, lean_object* v_i_1474_, lean_object* v_k_1475_){
_start:
{
lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = lean_array_get_size(v_keys_1472_);
v___x_1477_ = lean_nat_dec_lt(v_i_1474_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; 
lean_dec(v_i_1474_);
v___x_1478_ = lean_box(0);
return v___x_1478_;
}
else
{
lean_object* v_k_x27_1479_; uint8_t v___x_1480_; 
v_k_x27_1479_ = lean_array_fget_borrowed(v_keys_1472_, v_i_1474_);
v___x_1480_ = lean_name_eq(v_k_1475_, v_k_x27_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_add(v_i_1474_, v___x_1481_);
lean_dec(v_i_1474_);
v_i_1474_ = v___x_1482_;
goto _start;
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_array_fget_borrowed(v_vals_1473_, v_i_1474_);
lean_dec(v_i_1474_);
lean_inc(v___x_1484_);
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_keys_1486_, lean_object* v_vals_1487_, lean_object* v_i_1488_, lean_object* v_k_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_keys_1486_, v_vals_1487_, v_i_1488_, v_k_1489_);
lean_dec(v_k_1489_);
lean_dec_ref(v_vals_1487_);
lean_dec_ref(v_keys_1486_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(lean_object* v_x_1491_, size_t v_x_1492_, lean_object* v_x_1493_){
_start:
{
if (lean_obj_tag(v_x_1491_) == 0)
{
lean_object* v_es_1494_; lean_object* v___x_1495_; size_t v___x_1496_; size_t v___x_1497_; lean_object* v_j_1498_; lean_object* v___x_1499_; 
v_es_1494_ = lean_ctor_get(v_x_1491_, 0);
v___x_1495_ = lean_box(2);
v___x_1496_ = ((size_t)31ULL);
v___x_1497_ = lean_usize_land(v_x_1492_, v___x_1496_);
v_j_1498_ = lean_usize_to_nat(v___x_1497_);
v___x_1499_ = lean_array_get_borrowed(v___x_1495_, v_es_1494_, v_j_1498_);
lean_dec(v_j_1498_);
switch(lean_obj_tag(v___x_1499_))
{
case 0:
{
lean_object* v_key_1500_; lean_object* v_val_1501_; uint8_t v___x_1502_; 
v_key_1500_ = lean_ctor_get(v___x_1499_, 0);
v_val_1501_ = lean_ctor_get(v___x_1499_, 1);
v___x_1502_ = lean_name_eq(v_x_1493_, v_key_1500_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_box(0);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; 
lean_inc(v_val_1501_);
v___x_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_val_1501_);
return v___x_1504_;
}
}
case 1:
{
lean_object* v_node_1505_; size_t v___x_1506_; size_t v___x_1507_; 
v_node_1505_ = lean_ctor_get(v___x_1499_, 0);
v___x_1506_ = ((size_t)5ULL);
v___x_1507_ = lean_usize_shift_right(v_x_1492_, v___x_1506_);
v_x_1491_ = v_node_1505_;
v_x_1492_ = v___x_1507_;
goto _start;
}
default: 
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_box(0);
return v___x_1509_;
}
}
}
else
{
lean_object* v_ks_1510_; lean_object* v_vs_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_ks_1510_ = lean_ctor_get(v_x_1491_, 0);
v_vs_1511_ = lean_ctor_get(v_x_1491_, 1);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_ks_1510_, v_vs_1511_, v___x_1512_, v_x_1493_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___boxed(lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_){
_start:
{
size_t v_x_18782__boxed_1517_; lean_object* v_res_1518_; 
v_x_18782__boxed_1517_ = lean_unbox_usize(v_x_1515_);
lean_dec(v_x_1515_);
v_res_1518_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1514_, v_x_18782__boxed_1517_, v_x_1516_);
lean_dec(v_x_1516_);
lean_dec_ref(v_x_1514_);
return v_res_1518_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1519_; uint64_t v___x_1520_; 
v___x_1519_ = lean_unsigned_to_nat(1723u);
v___x_1520_ = lean_uint64_of_nat(v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(lean_object* v_x_1521_, lean_object* v_x_1522_){
_start:
{
uint64_t v___y_1524_; 
if (lean_obj_tag(v_x_1522_) == 0)
{
uint64_t v___x_1527_; 
v___x_1527_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0);
v___y_1524_ = v___x_1527_;
goto v___jp_1523_;
}
else
{
uint64_t v_hash_1528_; 
v_hash_1528_ = lean_ctor_get_uint64(v_x_1522_, sizeof(void*)*2);
v___y_1524_ = v_hash_1528_;
goto v___jp_1523_;
}
v___jp_1523_:
{
size_t v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_uint64_to_usize(v___y_1524_);
v___x_1526_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1521_, v___x_1525_, v_x_1522_);
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___boxed(lean_object* v_x_1529_, lean_object* v_x_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1529_, v_x_1530_);
lean_dec(v_x_1530_);
lean_dec_ref(v_x_1529_);
return v_res_1531_;
}
}
static lean_object* _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(lean_object* v___x_1535_, uint8_t v___x_1536_, lean_object* v___x_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
if (lean_obj_tag(v_a_1538_) == 0)
{
lean_object* v___x_1540_; 
lean_dec_ref(v___x_1537_);
v___x_1540_ = lean_array_to_list(v_a_1539_);
return v___x_1540_;
}
else
{
lean_object* v_head_1541_; lean_object* v_tail_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1582_; 
v_head_1541_ = lean_ctor_get(v_a_1538_, 0);
v_tail_1542_ = lean_ctor_get(v_a_1538_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_a_1538_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1544_ = v_a_1538_;
v_isShared_1545_ = v_isSharedCheck_1582_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_tail_1542_);
lean_inc(v_head_1541_);
lean_dec(v_a_1538_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1582_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_fst_1546_; lean_object* v_snd_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1581_; 
v_fst_1546_ = lean_ctor_get(v_head_1541_, 0);
v_snd_1547_ = lean_ctor_get(v_head_1541_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_head_1541_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1549_ = v_head_1541_;
v_isShared_1550_ = v_isSharedCheck_1581_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_snd_1547_);
lean_inc(v_fst_1546_);
lean_dec(v_head_1541_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1581_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___y_1552_; lean_object* v___y_1567_; uint8_t v___y_1568_; lean_object* v_unfoldAxiomCounter_1570_; lean_object* v___x_1571_; lean_object* v___y_1573_; lean_object* v___x_1579_; 
v_unfoldAxiomCounter_1570_ = lean_ctor_get(v___x_1535_, 1);
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1579_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_unfoldAxiomCounter_1570_, v_fst_1546_);
if (lean_obj_tag(v___x_1579_) == 0)
{
v___y_1573_ = v___x_1571_;
goto v___jp_1572_;
}
else
{
lean_object* v_val_1580_; 
v_val_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___y_1573_ = v_val_1580_;
goto v___jp_1572_;
}
v___jp_1551_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1553_ = l_Lean_MessageData_ofConstName(v_fst_1546_, v___x_1536_);
v___x_1554_ = lean_obj_once(&l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1, &l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1_once, _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1);
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 7);
lean_ctor_set(v___x_1549_, 1, v___x_1554_);
lean_ctor_set(v___x_1549_, 0, v___x_1553_);
v___x_1556_ = v___x_1549_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1557_ = l_Nat_reprFast(v___y_1552_);
v___x_1558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
v___x_1559_ = l_Lean_MessageData_ofFormat(v___x_1558_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 7);
lean_ctor_set(v___x_1544_, 1, v___x_1559_);
lean_ctor_set(v___x_1544_, 0, v___x_1556_);
v___x_1561_ = v___x_1544_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_array_push(v_a_1539_, v___x_1561_);
v_a_1538_ = v_tail_1542_;
v_a_1539_ = v___x_1562_;
goto _start;
}
}
}
v___jp_1566_:
{
if (v___y_1568_ == 0)
{
lean_dec(v___y_1567_);
lean_del_object(v___x_1549_);
lean_dec(v_fst_1546_);
lean_del_object(v___x_1544_);
v_a_1538_ = v_tail_1542_;
goto _start;
}
else
{
v___y_1552_ = v___y_1567_;
goto v___jp_1551_;
}
}
v___jp_1572_:
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = lean_nat_sub(v_snd_1547_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec(v_snd_1547_);
v___x_1575_ = lean_nat_dec_lt(v___x_1571_, v___x_1574_);
if (v___x_1575_ == 0)
{
v___y_1567_ = v___x_1574_;
v___y_1568_ = v___x_1575_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1576_; 
lean_inc(v_fst_1546_);
lean_inc_ref(v___x_1537_);
v___x_1576_ = l_Lean_getOriginalConstKind_x3f(v___x_1537_, v_fst_1546_);
if (lean_obj_tag(v___x_1576_) == 1)
{
lean_object* v_val_1577_; uint8_t v___x_1578_; 
v_val_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = lean_unbox(v_val_1577_);
lean_dec(v_val_1577_);
if (v___x_1578_ == 0)
{
v___y_1552_ = v___x_1574_;
goto v___jp_1551_;
}
else
{
v___y_1567_ = v___x_1574_;
v___y_1568_ = v___x_1536_;
goto v___jp_1566_;
}
}
else
{
lean_dec(v___x_1576_);
v___y_1567_ = v___x_1574_;
v___y_1568_ = v___x_1536_;
goto v___jp_1566_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___boxed(lean_object* v___x_1583_, lean_object* v___x_1584_, lean_object* v___x_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
uint8_t v___x_18857__boxed_1588_; lean_object* v_res_1589_; 
v___x_18857__boxed_1588_ = lean_unbox(v___x_1584_);
v_res_1589_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v___x_1583_, v___x_18857__boxed_1588_, v___x_1585_, v_a_1586_, v_a_1587_);
lean_dec_ref(v___x_1583_);
return v_res_1589_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__0));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__2));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__4));
v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__6));
v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__8));
v___x_1604_ = l_Lean_stringToMessageData(v___x_1603_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__11));
v___x_1609_ = l_Lean_stringToMessageData(v___x_1608_);
return v___x_1609_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_box(1);
v___x_1611_ = l_Lean_MessageData_ofFormat(v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__14));
v___x_1614_ = l_Lean_stringToMessageData(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object* v_type_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_inc_ref(v_type_1615_);
v___x_1621_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed), 6, 1);
lean_closure_set(v___x_1621_, 0, v_type_1615_);
v___x_1622_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1793_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1793_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1793_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v_env_1628_; lean_object* v___x_1629_; uint8_t v_isModule_1630_; 
v___x_1627_ = lean_st_ref_get(v_a_1619_);
v_env_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc_ref(v_env_1628_);
lean_dec(v___x_1627_);
v___x_1629_ = l_Lean_Environment_header(v_env_1628_);
lean_dec_ref(v_env_1628_);
v_isModule_1630_ = lean_ctor_get_uint8(v___x_1629_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1629_);
if (v_isModule_1630_ == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref(v___x_1621_);
if (v_isShared_1626_ == 0)
{
v___x_1632_ = v___x_1625_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1623_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
else
{
lean_object* v___x_1634_; 
lean_del_object(v___x_1625_);
lean_inc_ref(v___x_1621_);
v___x_1634_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1621_, v_isModule_1630_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1779_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1779_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1779_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_expr_eqv(v_a_1623_, v_a_1635_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_diag_1642_; lean_object* v_fileName_1643_; lean_object* v_fileMap_1644_; lean_object* v_options_1645_; lean_object* v_currRecDepth_1646_; lean_object* v_ref_1647_; lean_object* v_currNamespace_1648_; lean_object* v_openDecls_1649_; lean_object* v_initHeartbeats_1650_; lean_object* v_maxHeartbeats_1651_; lean_object* v_quotContext_1652_; lean_object* v_currMacroScope_1653_; lean_object* v_cancelTk_x3f_1654_; uint8_t v_suppressElabErrors_1655_; lean_object* v_inheritedTraceOptions_1656_; lean_object* v_env_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v_a_1672_; lean_object* v___y_1718_; uint8_t v___y_1719_; uint8_t v___x_1730_; lean_object* v_fileName_1732_; lean_object* v_fileMap_1733_; lean_object* v_currRecDepth_1734_; lean_object* v_ref_1735_; lean_object* v_currNamespace_1736_; lean_object* v_openDecls_1737_; lean_object* v_initHeartbeats_1738_; lean_object* v_maxHeartbeats_1739_; lean_object* v_quotContext_1740_; lean_object* v_currMacroScope_1741_; lean_object* v_cancelTk_x3f_1742_; uint8_t v_suppressElabErrors_1743_; lean_object* v_inheritedTraceOptions_1744_; lean_object* v___y_1745_; uint8_t v___y_1754_; uint8_t v___x_1775_; 
lean_del_object(v___x_1637_);
v___x_1640_ = lean_st_ref_get(v_a_1617_);
v___x_1641_ = lean_st_ref_get(v_a_1619_);
v_diag_1642_ = lean_ctor_get(v___x_1640_, 4);
lean_inc_ref(v_diag_1642_);
lean_dec(v___x_1640_);
v_fileName_1643_ = lean_ctor_get(v_a_1618_, 0);
v_fileMap_1644_ = lean_ctor_get(v_a_1618_, 1);
v_options_1645_ = lean_ctor_get(v_a_1618_, 2);
v_currRecDepth_1646_ = lean_ctor_get(v_a_1618_, 3);
v_ref_1647_ = lean_ctor_get(v_a_1618_, 5);
v_currNamespace_1648_ = lean_ctor_get(v_a_1618_, 6);
v_openDecls_1649_ = lean_ctor_get(v_a_1618_, 7);
v_initHeartbeats_1650_ = lean_ctor_get(v_a_1618_, 8);
v_maxHeartbeats_1651_ = lean_ctor_get(v_a_1618_, 9);
v_quotContext_1652_ = lean_ctor_get(v_a_1618_, 10);
v_currMacroScope_1653_ = lean_ctor_get(v_a_1618_, 11);
v_cancelTk_x3f_1654_ = lean_ctor_get(v_a_1618_, 12);
v_suppressElabErrors_1655_ = lean_ctor_get_uint8(v_a_1618_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1656_ = lean_ctor_get(v_a_1618_, 13);
v_env_1657_ = lean_ctor_get(v___x_1641_, 0);
lean_inc_ref(v_env_1657_);
lean_dec(v___x_1641_);
v___x_1658_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1645_);
v___x_1659_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v_options_1645_, v___x_1658_, v_isModule_1630_);
v___x_1660_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__1, &l_Lean_Compiler_LCNF_toLCNFType___closed__1_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1);
v___x_1661_ = l_Lean_MessageData_ofExpr(v_a_1623_);
v___x_1662_ = l_Lean_indentD(v___x_1661_);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1660_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__3, &l_Lean_Compiler_LCNF_toLCNFType___closed__3_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = l_Lean_MessageData_ofExpr(v_a_1635_);
v___x_1667_ = l_Lean_indentD(v___x_1666_);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1665_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__5, &l_Lean_Compiler_LCNF_toLCNFType___closed__5_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1730_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v___x_1659_, v___x_1658_);
v___x_1775_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1657_);
lean_dec_ref(v_env_1657_);
if (v___x_1775_ == 0)
{
if (v___x_1730_ == 0)
{
v_fileName_1732_ = v_fileName_1643_;
v_fileMap_1733_ = v_fileMap_1644_;
v_currRecDepth_1734_ = v_currRecDepth_1646_;
v_ref_1735_ = v_ref_1647_;
v_currNamespace_1736_ = v_currNamespace_1648_;
v_openDecls_1737_ = v_openDecls_1649_;
v_initHeartbeats_1738_ = v_initHeartbeats_1650_;
v_maxHeartbeats_1739_ = v_maxHeartbeats_1651_;
v_quotContext_1740_ = v_quotContext_1652_;
v_currMacroScope_1741_ = v_currMacroScope_1653_;
v_cancelTk_x3f_1742_ = v_cancelTk_x3f_1654_;
v_suppressElabErrors_1743_ = v_suppressElabErrors_1655_;
v_inheritedTraceOptions_1744_ = v_inheritedTraceOptions_1656_;
v___y_1745_ = v_a_1619_;
goto v___jp_1731_;
}
else
{
v___y_1754_ = v___x_1775_;
goto v___jp_1753_;
}
}
else
{
v___y_1754_ = v___x_1730_;
goto v___jp_1753_;
}
v___jp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v_snd_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1694_; 
lean_inc_ref(v_a_1672_);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_a_1672_);
v___x_1674_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1617_, v_diag_1642_, v___x_1673_);
lean_dec_ref_known(v___x_1673_, 1);
lean_dec_ref(v___x_1674_);
v_snd_1675_ = lean_ctor_get(v_a_1672_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_a_1672_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v_a_1672_, 0);
lean_dec(v_unused_1695_);
v___x_1677_ = v_a_1672_;
v_isShared_1678_ = v_isSharedCheck_1694_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_snd_1675_);
lean_dec(v_a_1672_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1694_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__7, &l_Lean_Compiler_LCNF_toLCNFType___closed__7_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7);
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 7);
lean_ctor_set(v___x_1677_, 0, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_snd_1675_);
v___x_1681_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v___x_1682_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__9, &l_Lean_Compiler_LCNF_toLCNFType___closed__9_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9);
v___x_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_1683_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
v___jp_1696_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v_diag_1699_; lean_object* v_env_1700_; lean_object* v_unfoldAxiomCounter_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1697_ = lean_st_ref_get(v_a_1619_);
v___x_1698_ = lean_st_ref_get(v_a_1617_);
v_diag_1699_ = lean_ctor_get(v___x_1698_, 4);
lean_inc_ref(v_diag_1699_);
lean_dec(v___x_1698_);
v_env_1700_ = lean_ctor_get(v___x_1697_, 0);
lean_inc_ref(v_env_1700_);
lean_dec(v___x_1697_);
v_unfoldAxiomCounter_1701_ = lean_ctor_get(v_diag_1699_, 1);
lean_inc_ref(v_unfoldAxiomCounter_1701_);
lean_dec_ref(v_diag_1699_);
v___x_1702_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_unfoldAxiomCounter_1701_);
lean_dec_ref(v_unfoldAxiomCounter_1701_);
v___x_1703_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__10));
v___x_1704_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v_diag_1642_, v___x_1639_, v_env_1700_, v___x_1702_, v___x_1703_);
v___x_1705_ = l_List_isEmpty___redArg(v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref_known(v___x_1670_, 2);
v___x_1706_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__12, &l_Lean_Compiler_LCNF_toLCNFType___closed__12_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12);
v___x_1707_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__13, &l_Lean_Compiler_LCNF_toLCNFType___closed__13_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13);
v___x_1708_ = l_Lean_MessageData_joinSep(v___x_1704_, v___x_1707_);
v___x_1709_ = l_Lean_indentD(v___x_1708_);
v___x_1710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1706_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__15, &l_Lean_Compiler_LCNF_toLCNFType___closed__15_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15);
v___x_1712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v___x_1712_);
v_a_1672_ = v___x_1714_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec(v___x_1704_);
v___x_1715_ = lean_box(0);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v___x_1670_);
v_a_1672_ = v___x_1716_;
goto v___jp_1671_;
}
}
v___jp_1717_:
{
if (v___y_1719_ == 0)
{
lean_dec_ref(v___y_1718_);
goto v___jp_1696_;
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref_known(v___x_1670_, 2);
v___x_1720_ = lean_box(0);
v___x_1721_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1617_, v_diag_1642_, v___x_1720_);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v___x_1721_, 0);
lean_dec(v_unused_1729_);
v___x_1723_ = v___x_1721_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_dec(v___x_1721_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 1);
lean_ctor_set(v___x_1723_, 0, v___y_1718_);
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___y_1718_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
v___jp_1731_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1746_ = l_Lean_maxRecDepth;
v___x_1747_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(v___x_1659_, v___x_1746_);
lean_inc_ref(v_inheritedTraceOptions_1744_);
lean_inc(v_cancelTk_x3f_1742_);
lean_inc(v_currMacroScope_1741_);
lean_inc(v_quotContext_1740_);
lean_inc(v_maxHeartbeats_1739_);
lean_inc(v_initHeartbeats_1738_);
lean_inc(v_openDecls_1737_);
lean_inc(v_currNamespace_1736_);
lean_inc(v_ref_1735_);
lean_inc(v_currRecDepth_1734_);
lean_inc_ref(v_fileMap_1733_);
lean_inc_ref(v_fileName_1732_);
v___x_1748_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1748_, 0, v_fileName_1732_);
lean_ctor_set(v___x_1748_, 1, v_fileMap_1733_);
lean_ctor_set(v___x_1748_, 2, v___x_1659_);
lean_ctor_set(v___x_1748_, 3, v_currRecDepth_1734_);
lean_ctor_set(v___x_1748_, 4, v___x_1747_);
lean_ctor_set(v___x_1748_, 5, v_ref_1735_);
lean_ctor_set(v___x_1748_, 6, v_currNamespace_1736_);
lean_ctor_set(v___x_1748_, 7, v_openDecls_1737_);
lean_ctor_set(v___x_1748_, 8, v_initHeartbeats_1738_);
lean_ctor_set(v___x_1748_, 9, v_maxHeartbeats_1739_);
lean_ctor_set(v___x_1748_, 10, v_quotContext_1740_);
lean_ctor_set(v___x_1748_, 11, v_currMacroScope_1741_);
lean_ctor_set(v___x_1748_, 12, v_cancelTk_x3f_1742_);
lean_ctor_set(v___x_1748_, 13, v_inheritedTraceOptions_1744_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*14, v___x_1730_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*14 + 1, v_suppressElabErrors_1743_);
v___x_1749_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1621_, v_isModule_1630_, v_a_1616_, v_a_1617_, v___x_1748_, v___y_1745_);
lean_dec_ref_known(v___x_1748_, 14);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_dec_ref_known(v___x_1749_, 1);
goto v___jp_1696_;
}
else
{
lean_object* v_a_1750_; uint8_t v___x_1751_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = l_Lean_Exception_isInterrupt(v_a_1750_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; 
lean_inc(v_a_1750_);
v___x_1752_ = l_Lean_Exception_isRuntime(v_a_1750_);
v___y_1718_ = v_a_1750_;
v___y_1719_ = v___x_1752_;
goto v___jp_1717_;
}
else
{
v___y_1718_ = v_a_1750_;
v___y_1719_ = v___x_1751_;
goto v___jp_1717_;
}
}
}
v___jp_1753_:
{
if (v___y_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v_env_1756_; lean_object* v_nextMacroScope_1757_; lean_object* v_ngen_1758_; lean_object* v_auxDeclNGen_1759_; lean_object* v_traceState_1760_; lean_object* v_messages_1761_; lean_object* v_infoState_1762_; lean_object* v_snapshotTasks_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1773_; 
v___x_1755_ = lean_st_ref_take(v_a_1619_);
v_env_1756_ = lean_ctor_get(v___x_1755_, 0);
v_nextMacroScope_1757_ = lean_ctor_get(v___x_1755_, 1);
v_ngen_1758_ = lean_ctor_get(v___x_1755_, 2);
v_auxDeclNGen_1759_ = lean_ctor_get(v___x_1755_, 3);
v_traceState_1760_ = lean_ctor_get(v___x_1755_, 4);
v_messages_1761_ = lean_ctor_get(v___x_1755_, 6);
v_infoState_1762_ = lean_ctor_get(v___x_1755_, 7);
v_snapshotTasks_1763_ = lean_ctor_get(v___x_1755_, 8);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v___x_1755_, 5);
lean_dec(v_unused_1774_);
v___x_1765_ = v___x_1755_;
v_isShared_1766_ = v_isSharedCheck_1773_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snapshotTasks_1763_);
lean_inc(v_infoState_1762_);
lean_inc(v_messages_1761_);
lean_inc(v_traceState_1760_);
lean_inc(v_auxDeclNGen_1759_);
lean_inc(v_ngen_1758_);
lean_inc(v_nextMacroScope_1757_);
lean_inc(v_env_1756_);
lean_dec(v___x_1755_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1773_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1767_ = l_Lean_Kernel_enableDiag(v_env_1756_, v___x_1730_);
v___x_1768_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 5, v___x_1768_);
lean_ctor_set(v___x_1765_, 0, v___x_1767_);
v___x_1770_ = v___x_1765_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_nextMacroScope_1757_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_ngen_1758_);
lean_ctor_set(v_reuseFailAlloc_1772_, 3, v_auxDeclNGen_1759_);
lean_ctor_set(v_reuseFailAlloc_1772_, 4, v_traceState_1760_);
lean_ctor_set(v_reuseFailAlloc_1772_, 5, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1772_, 6, v_messages_1761_);
lean_ctor_set(v_reuseFailAlloc_1772_, 7, v_infoState_1762_);
lean_ctor_set(v_reuseFailAlloc_1772_, 8, v_snapshotTasks_1763_);
v___x_1770_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_st_ref_set(v_a_1619_, v___x_1770_);
v_fileName_1732_ = v_fileName_1643_;
v_fileMap_1733_ = v_fileMap_1644_;
v_currRecDepth_1734_ = v_currRecDepth_1646_;
v_ref_1735_ = v_ref_1647_;
v_currNamespace_1736_ = v_currNamespace_1648_;
v_openDecls_1737_ = v_openDecls_1649_;
v_initHeartbeats_1738_ = v_initHeartbeats_1650_;
v_maxHeartbeats_1739_ = v_maxHeartbeats_1651_;
v_quotContext_1740_ = v_quotContext_1652_;
v_currMacroScope_1741_ = v_currMacroScope_1653_;
v_cancelTk_x3f_1742_ = v_cancelTk_x3f_1654_;
v_suppressElabErrors_1743_ = v_suppressElabErrors_1655_;
v_inheritedTraceOptions_1744_ = v_inheritedTraceOptions_1656_;
v___y_1745_ = v_a_1619_;
goto v___jp_1731_;
}
}
}
else
{
v_fileName_1732_ = v_fileName_1643_;
v_fileMap_1733_ = v_fileMap_1644_;
v_currRecDepth_1734_ = v_currRecDepth_1646_;
v_ref_1735_ = v_ref_1647_;
v_currNamespace_1736_ = v_currNamespace_1648_;
v_openDecls_1737_ = v_openDecls_1649_;
v_initHeartbeats_1738_ = v_initHeartbeats_1650_;
v_maxHeartbeats_1739_ = v_maxHeartbeats_1651_;
v_quotContext_1740_ = v_quotContext_1652_;
v_currMacroScope_1741_ = v_currMacroScope_1653_;
v_cancelTk_x3f_1742_ = v_cancelTk_x3f_1654_;
v_suppressElabErrors_1743_ = v_suppressElabErrors_1655_;
v_inheritedTraceOptions_1744_ = v_inheritedTraceOptions_1656_;
v___y_1745_ = v_a_1619_;
goto v___jp_1731_;
}
}
}
else
{
lean_object* v___x_1777_; 
lean_dec(v_a_1635_);
lean_dec_ref(v___x_1621_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v_a_1623_);
v___x_1777_ = v___x_1637_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1623_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_a_1780_; uint8_t v___y_1782_; uint8_t v___x_1791_; 
lean_dec_ref(v___x_1621_);
v_a_1780_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1780_);
v___x_1791_ = l_Lean_Exception_isInterrupt(v_a_1780_);
if (v___x_1791_ == 0)
{
uint8_t v___x_1792_; 
v___x_1792_ = l_Lean_Exception_isRuntime(v_a_1780_);
v___y_1782_ = v___x_1792_;
goto v___jp_1781_;
}
else
{
lean_dec(v_a_1780_);
v___y_1782_ = v___x_1791_;
goto v___jp_1781_;
}
v___jp_1781_:
{
if (v___y_1782_ == 0)
{
lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v___x_1634_, 0);
lean_dec(v_unused_1790_);
v___x_1784_ = v___x_1634_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_dec(v___x_1634_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 0);
lean_ctor_set(v___x_1784_, 0, v_a_1623_);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1623_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
else
{
lean_dec(v_a_1623_);
return v___x_1634_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1621_);
return v___x_1622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___boxed(lean_object* v_type_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Compiler_LCNF_toLCNFType(v_type_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(lean_object* v_00_u03b2_1801_, lean_object* v_x_1802_, lean_object* v_x_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1802_, v_x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___boxed(lean_object* v_00_u03b2_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(v_00_u03b2_1805_, v_x_1806_, v_x_1807_);
lean_dec(v_x_1807_);
lean_dec_ref(v_x_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(lean_object* v_00_u03b2_1809_, lean_object* v_m_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___boxed(lean_object* v_00_u03b2_1812_, lean_object* v_m_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(v_00_u03b2_1812_, v_m_1813_);
lean_dec_ref(v_m_1813_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(lean_object* v_00_u03b2_1815_, lean_object* v_x_1816_, size_t v_x_1817_, lean_object* v_x_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1816_, v_x_1817_, v_x_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_){
_start:
{
size_t v_x_19319__boxed_1824_; lean_object* v_res_1825_; 
v_x_19319__boxed_1824_ = lean_unbox_usize(v_x_1822_);
lean_dec(v_x_1822_);
v_res_1825_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(v_00_u03b2_1820_, v_x_1821_, v_x_19319__boxed_1824_, v_x_1823_);
lean_dec(v_x_1823_);
lean_dec_ref(v_x_1821_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(lean_object* v_00_u03c3_1826_, lean_object* v_00_u03b2_1827_, lean_object* v_map_1828_, lean_object* v_f_1829_, lean_object* v_init_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_1828_, v_f_1829_, v_init_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1832_, lean_object* v_00_u03b2_1833_, lean_object* v_map_1834_, lean_object* v_f_1835_, lean_object* v_init_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(v_00_u03c3_1832_, v_00_u03b2_1833_, v_map_1834_, v_f_1835_, v_init_1836_);
lean_dec_ref(v_map_1834_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1838_, lean_object* v_keys_1839_, lean_object* v_vals_1840_, lean_object* v_heq_1841_, lean_object* v_i_1842_, lean_object* v_k_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_keys_1839_, v_vals_1840_, v_i_1842_, v_k_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1845_, lean_object* v_keys_1846_, lean_object* v_vals_1847_, lean_object* v_heq_1848_, lean_object* v_i_1849_, lean_object* v_k_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(v_00_u03b2_1845_, v_keys_1846_, v_vals_1847_, v_heq_1848_, v_i_1849_, v_k_1850_);
lean_dec(v_k_1850_);
lean_dec_ref(v_vals_1847_);
lean_dec_ref(v_keys_1846_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(lean_object* v_map_1852_, lean_object* v_f_1853_, lean_object* v_init_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1853_, v_map_1852_, v_init_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_map_1856_, lean_object* v_f_1857_, lean_object* v_init_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(v_map_1856_, v_f_1857_, v_init_1858_);
lean_dec_ref(v_map_1856_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(lean_object* v_00_u03c3_1860_, lean_object* v_00_u03b2_1861_, lean_object* v_map_1862_, lean_object* v_f_1863_, lean_object* v_init_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1863_, v_map_1862_, v_init_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03c3_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_map_1868_, lean_object* v_f_1869_, lean_object* v_init_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(v_00_u03c3_1866_, v_00_u03b2_1867_, v_map_1868_, v_f_1869_, v_init_1870_);
lean_dec_ref(v_map_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(lean_object* v_00_u03c3_1872_, lean_object* v_00_u03b1_1873_, lean_object* v_00_u03b2_1874_, lean_object* v_f_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1875_, v_x_1876_, v_x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03c3_1879_, lean_object* v_00_u03b1_1880_, lean_object* v_00_u03b2_1881_, lean_object* v_f_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(v_00_u03c3_1879_, v_00_u03b1_1880_, v_00_u03b2_1881_, v_f_1882_, v_x_1883_, v_x_1884_);
lean_dec_ref(v_x_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(lean_object* v_00_u03b1_1886_, lean_object* v_00_u03b2_1887_, lean_object* v_00_u03c3_1888_, lean_object* v_f_1889_, lean_object* v_as_1890_, size_t v_i_1891_, size_t v_stop_1892_, lean_object* v_b_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1889_, v_as_1890_, v_i_1891_, v_stop_1892_, v_b_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___boxed(lean_object* v_00_u03b1_1895_, lean_object* v_00_u03b2_1896_, lean_object* v_00_u03c3_1897_, lean_object* v_f_1898_, lean_object* v_as_1899_, lean_object* v_i_1900_, lean_object* v_stop_1901_, lean_object* v_b_1902_){
_start:
{
size_t v_i_boxed_1903_; size_t v_stop_boxed_1904_; lean_object* v_res_1905_; 
v_i_boxed_1903_ = lean_unbox_usize(v_i_1900_);
lean_dec(v_i_1900_);
v_stop_boxed_1904_ = lean_unbox_usize(v_stop_1901_);
lean_dec(v_stop_1901_);
v_res_1905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(v_00_u03b1_1895_, v_00_u03b2_1896_, v_00_u03c3_1897_, v_f_1898_, v_as_1899_, v_i_boxed_1903_, v_stop_boxed_1904_, v_b_1902_);
lean_dec_ref(v_as_1899_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(lean_object* v_00_u03c3_1906_, lean_object* v_00_u03b1_1907_, lean_object* v_00_u03b2_1908_, lean_object* v_f_1909_, lean_object* v_keys_1910_, lean_object* v_vals_1911_, lean_object* v_heq_1912_, lean_object* v_i_1913_, lean_object* v_acc_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1909_, v_keys_1910_, v_vals_1911_, v_i_1913_, v_acc_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___boxed(lean_object* v_00_u03c3_1916_, lean_object* v_00_u03b1_1917_, lean_object* v_00_u03b2_1918_, lean_object* v_f_1919_, lean_object* v_keys_1920_, lean_object* v_vals_1921_, lean_object* v_heq_1922_, lean_object* v_i_1923_, lean_object* v_acc_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(v_00_u03c3_1916_, v_00_u03b1_1917_, v_00_u03b2_1918_, v_f_1919_, v_keys_1920_, v_vals_1921_, v_heq_1922_, v_i_1923_, v_acc_1924_);
lean_dec_ref(v_vals_1921_);
lean_dec_ref(v_keys_1920_);
return v_res_1925_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f(lean_object* v_a_1930_, lean_object* v_b_1931_){
_start:
{
lean_object* v___y_1935_; uint8_t v___y_1938_; uint8_t v___x_2011_; 
v___x_2011_ = l_Lean_Expr_isErased(v_a_1930_);
if (v___x_2011_ == 0)
{
uint8_t v___x_2012_; 
v___x_2012_ = l_Lean_Expr_isErased(v_b_1931_);
v___y_1938_ = v___x_2012_;
goto v___jp_1937_;
}
else
{
v___y_1938_ = v___x_2011_;
goto v___jp_1937_;
}
v___jp_1932_:
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1933_;
}
v___jp_1934_:
{
if (lean_obj_tag(v___y_1935_) == 0)
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1936_;
}
else
{
return v___y_1935_;
}
}
v___jp_1937_:
{
if (v___y_1938_ == 0)
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_expr_eqv(v_a_1930_, v_b_1931_);
if (v___x_1939_ == 0)
{
lean_object* v_a_x27_1940_; lean_object* v_b_x27_1941_; uint8_t v___x_1942_; 
lean_inc_ref(v_a_1930_);
v_a_x27_1940_ = l_Lean_Expr_headBeta(v_a_1930_);
lean_inc_ref(v_b_1931_);
v_b_x27_1941_ = l_Lean_Expr_headBeta(v_b_1931_);
v___x_1942_ = lean_expr_eqv(v_a_1930_, v_a_x27_1940_);
if (v___x_1942_ == 0)
{
lean_dec_ref(v_b_1931_);
lean_dec_ref(v_a_1930_);
v_a_1930_ = v_a_x27_1940_;
v_b_1931_ = v_b_x27_1941_;
goto _start;
}
else
{
if (v___x_1939_ == 0)
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_expr_eqv(v_b_1931_, v_b_x27_1941_);
if (v___x_1944_ == 0)
{
lean_dec_ref(v_b_1931_);
lean_dec_ref(v_a_1930_);
v_a_1930_ = v_a_x27_1940_;
v_b_1931_ = v_b_x27_1941_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_1941_);
lean_dec_ref(v_a_x27_1940_);
switch(lean_obj_tag(v_a_1930_))
{
case 10:
{
lean_object* v_expr_1946_; 
v_expr_1946_ = lean_ctor_get(v_a_1930_, 1);
lean_inc_ref(v_expr_1946_);
lean_dec_ref_known(v_a_1930_, 2);
v_a_1930_ = v_expr_1946_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_1931_))
{
case 10:
{
lean_object* v_expr_1948_; 
v_expr_1948_ = lean_ctor_get(v_b_1931_, 1);
lean_inc_ref(v_expr_1948_);
lean_dec_ref_known(v_b_1931_, 2);
v_b_1931_ = v_expr_1948_;
goto _start;
}
case 5:
{
lean_object* v_fn_1950_; lean_object* v_arg_1951_; lean_object* v_fn_1952_; lean_object* v_arg_1953_; lean_object* v___x_1954_; 
v_fn_1950_ = lean_ctor_get(v_a_1930_, 0);
lean_inc_ref(v_fn_1950_);
v_arg_1951_ = lean_ctor_get(v_a_1930_, 1);
lean_inc_ref(v_arg_1951_);
lean_dec_ref_known(v_a_1930_, 2);
v_fn_1952_ = lean_ctor_get(v_b_1931_, 0);
lean_inc_ref(v_fn_1952_);
v_arg_1953_ = lean_ctor_get(v_b_1931_, 1);
lean_inc_ref(v_arg_1953_);
lean_dec_ref_known(v_b_1931_, 2);
v___x_1954_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_fn_1950_, v_fn_1952_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_dec_ref(v_arg_1953_);
lean_dec_ref(v_arg_1951_);
v___y_1935_ = v___x_1954_;
goto v___jp_1934_;
}
else
{
lean_object* v_val_1955_; lean_object* v___x_1956_; 
v_val_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_arg_1951_, v_arg_1953_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_dec(v_val_1955_);
v___y_1935_ = v___x_1956_;
goto v___jp_1934_;
}
else
{
lean_object* v_val_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_val_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_val_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1961_ = l_Lean_Expr_app___override(v_val_1955_, v_val_1957_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_1930_, 2);
lean_dec_ref(v_b_1931_);
goto v___jp_1932_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_1931_))
{
case 10:
{
lean_object* v_expr_1966_; 
v_expr_1966_ = lean_ctor_get(v_b_1931_, 1);
lean_inc_ref(v_expr_1966_);
lean_dec_ref_known(v_b_1931_, 2);
v_b_1931_ = v_expr_1966_;
goto _start;
}
case 7:
{
lean_object* v_binderName_1968_; lean_object* v_binderType_1969_; lean_object* v_body_1970_; lean_object* v_binderType_1971_; lean_object* v_body_1972_; lean_object* v___x_1973_; 
v_binderName_1968_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_binderName_1968_);
v_binderType_1969_ = lean_ctor_get(v_a_1930_, 1);
lean_inc_ref(v_binderType_1969_);
v_body_1970_ = lean_ctor_get(v_a_1930_, 2);
lean_inc_ref(v_body_1970_);
lean_dec_ref_known(v_a_1930_, 3);
v_binderType_1971_ = lean_ctor_get(v_b_1931_, 1);
lean_inc_ref(v_binderType_1971_);
v_body_1972_ = lean_ctor_get(v_b_1931_, 2);
lean_inc_ref(v_body_1972_);
lean_dec_ref_known(v_b_1931_, 3);
v___x_1973_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_1969_, v_binderType_1971_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_dec_ref(v_body_1972_);
lean_dec_ref(v_body_1970_);
lean_dec(v_binderName_1968_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1974_;
}
else
{
return v___x_1973_;
}
}
else
{
lean_object* v_val_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1985_; 
v_val_1975_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1977_ = v___x_1973_;
v_isShared_1978_ = v_isSharedCheck_1985_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_val_1975_);
lean_dec(v___x_1973_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1985_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1979_ = l_Lean_Compiler_LCNF_joinTypes(v_body_1970_, v_body_1972_);
v___x_1980_ = 0;
v___x_1981_ = l_Lean_Expr_forallE___override(v_binderName_1968_, v_val_1975_, v___x_1979_, v___x_1980_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1981_);
v___x_1983_ = v___x_1977_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_1930_, 3);
lean_dec_ref(v_b_1931_);
goto v___jp_1932_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_1931_))
{
case 10:
{
lean_object* v_expr_1986_; 
v_expr_1986_ = lean_ctor_get(v_b_1931_, 1);
lean_inc_ref(v_expr_1986_);
lean_dec_ref_known(v_b_1931_, 2);
v_b_1931_ = v_expr_1986_;
goto _start;
}
case 6:
{
lean_object* v_binderName_1988_; lean_object* v_binderType_1989_; lean_object* v_body_1990_; lean_object* v_binderType_1991_; lean_object* v_body_1992_; lean_object* v___x_1993_; 
v_binderName_1988_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_binderName_1988_);
v_binderType_1989_ = lean_ctor_get(v_a_1930_, 1);
lean_inc_ref(v_binderType_1989_);
v_body_1990_ = lean_ctor_get(v_a_1930_, 2);
lean_inc_ref(v_body_1990_);
lean_dec_ref_known(v_a_1930_, 3);
v_binderType_1991_ = lean_ctor_get(v_b_1931_, 1);
lean_inc_ref(v_binderType_1991_);
v_body_1992_ = lean_ctor_get(v_b_1931_, 2);
lean_inc_ref(v_body_1992_);
lean_dec_ref_known(v_b_1931_, 3);
v___x_1993_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_1989_, v_binderType_1991_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_dec_ref(v_body_1992_);
lean_dec_ref(v_body_1990_);
lean_dec(v_binderName_1988_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1994_;
}
else
{
return v___x_1993_;
}
}
else
{
lean_object* v_val_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2005_; 
v_val_1995_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1997_ = v___x_1993_;
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_val_1995_);
lean_dec(v___x_1993_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; uint8_t v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_1999_ = l_Lean_Compiler_LCNF_joinTypes(v_body_1990_, v_body_1992_);
v___x_2000_ = 0;
v___x_2001_ = l_Lean_Expr_lam___override(v_binderName_1988_, v_val_1995_, v___x_1999_, v___x_2000_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2001_);
v___x_2003_ = v___x_1997_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_1930_, 3);
lean_dec_ref(v_b_1931_);
goto v___jp_1932_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_1931_) == 10)
{
lean_object* v_expr_2006_; 
v_expr_2006_ = lean_ctor_get(v_b_1931_, 1);
lean_inc_ref(v_expr_2006_);
lean_dec_ref_known(v_b_1931_, 2);
v_b_1931_ = v_expr_2006_;
goto _start;
}
else
{
lean_dec_ref(v_b_1931_);
lean_dec_ref(v_a_1930_);
goto v___jp_1932_;
}
}
}
}
}
else
{
lean_dec_ref(v_b_1931_);
lean_dec_ref(v_a_1930_);
v_a_1930_ = v_a_x27_1940_;
v_b_1931_ = v_b_x27_1941_;
goto _start;
}
}
}
else
{
lean_object* v___x_2009_; 
lean_dec_ref(v_b_1931_);
v___x_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2009_, 0, v_a_1930_);
return v___x_2009_;
}
}
else
{
lean_object* v___x_2010_; 
lean_dec_ref(v_b_1931_);
lean_dec_ref(v_a_1930_);
v___x_2010_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1);
return v___x_2010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object* v_a_2013_, lean_object* v_b_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_a_2013_, v_b_2014_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
return v___x_2016_;
}
else
{
lean_object* v_val_2017_; 
v_val_2017_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_val_2017_);
lean_dec_ref_known(v___x_2015_, 1);
return v_val_2017_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object* v_type_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_Expr_headBeta(v_type_2018_);
switch(lean_obj_tag(v___x_2019_))
{
case 3:
{
uint8_t v___x_2020_; 
lean_dec_ref_known(v___x_2019_, 1);
v___x_2020_ = 1;
return v___x_2020_;
}
case 7:
{
lean_object* v_body_2021_; 
v_body_2021_ = lean_ctor_get(v___x_2019_, 2);
lean_inc_ref(v_body_2021_);
lean_dec_ref_known(v___x_2019_, 3);
v_type_2018_ = v_body_2021_;
goto _start;
}
default: 
{
uint8_t v___x_2023_; 
lean_dec_ref(v___x_2019_);
v___x_2023_ = 0;
return v___x_2023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTypeFormerType___boxed(lean_object* v_type_2024_){
_start:
{
uint8_t v_res_2025_; lean_object* v_r_2026_; 
v_res_2025_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_2024_);
v_r_2026_ = lean_box(v_res_2025_);
return v_r_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(lean_object* v_msgData_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; lean_object* v_env_2032_; lean_object* v_options_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2031_ = lean_st_ref_get(v___y_2029_);
v_env_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc_ref(v_env_2032_);
lean_dec(v___x_2031_);
v_options_2033_ = lean_ctor_get(v___y_2028_, 2);
v___x_2034_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_2035_ = lean_unsigned_to_nat(32u);
v___x_2036_ = lean_mk_empty_array_with_capacity(v___x_2035_);
lean_dec_ref(v___x_2036_);
v___x_2037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_2033_);
v___x_2038_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2038_, 0, v_env_2032_);
lean_ctor_set(v___x_2038_, 1, v___x_2034_);
lean_ctor_set(v___x_2038_, 2, v___x_2037_);
lean_ctor_set(v___x_2038_, 3, v_options_2033_);
v___x_2039_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
lean_ctor_set(v___x_2039_, 1, v_msgData_2027_);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0___boxed(lean_object* v_msgData_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msgData_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(lean_object* v_msg_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_ref_2050_; lean_object* v___x_2051_; lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2060_; 
v_ref_2050_ = lean_ctor_get(v___y_2047_, 5);
v___x_2051_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msg_2046_, v___y_2047_, v___y_2048_);
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2060_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2060_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
lean_inc(v_ref_2050_);
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v_ref_2050_);
lean_ctor_set(v___x_2056_, 1, v_a_2052_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set_tag(v___x_2054_, 1);
lean_ctor_set(v___x_2054_, 0, v___x_2056_);
v___x_2058_ = v___x_2054_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg___boxed(lean_object* v_msg_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2065_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0));
v___x_2068_ = l_Lean_stringToMessageData(v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(lean_object* v_ps_2069_, lean_object* v_i_2070_, lean_object* v_type_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = lean_array_get_size(v_ps_2069_);
v___x_2076_ = lean_nat_dec_lt(v_i_2070_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
lean_dec(v_i_2070_);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v_type_2071_);
return v___x_2077_;
}
else
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Expr_headBeta(v_type_2071_);
if (lean_obj_tag(v___x_2078_) == 7)
{
lean_object* v_body_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v_body_2079_ = lean_ctor_get(v___x_2078_, 2);
lean_inc_ref(v_body_2079_);
lean_dec_ref_known(v___x_2078_, 3);
v___x_2080_ = lean_unsigned_to_nat(1u);
v___x_2081_ = lean_nat_add(v_i_2070_, v___x_2080_);
v___x_2082_ = lean_array_fget_borrowed(v_ps_2069_, v_i_2070_);
lean_dec(v_i_2070_);
v___x_2083_ = lean_expr_instantiate1(v_body_2079_, v___x_2082_);
lean_dec_ref(v_body_2079_);
v_i_2070_ = v___x_2081_;
v_type_2071_ = v___x_2083_;
goto _start;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec_ref(v___x_2078_);
lean_dec(v_i_2070_);
v___x_2085_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1);
v___x_2086_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v___x_2085_, v_a_2072_, v_a_2073_);
return v___x_2086_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object* v_ps_2087_, lean_object* v_i_2088_, lean_object* v_type_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2087_, v_i_2088_, v_type_2089_, v_a_2090_, v_a_2091_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
lean_dec_ref(v_ps_2087_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(lean_object* v_00_u03b1_2094_, lean_object* v_msg_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2095_, v___y_2096_, v___y_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___boxed(lean_object* v_00_u03b1_2100_, lean_object* v_msg_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(v_00_u03b1_2100_, v_msg_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter___redArg(lean_object* v_e_2106_, lean_object* v_h__1_2107_, lean_object* v_h__2_2108_){
_start:
{
if (lean_obj_tag(v_e_2106_) == 7)
{
lean_object* v_binderName_2109_; lean_object* v_binderType_2110_; lean_object* v_body_2111_; uint8_t v_binderInfo_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_dec(v_h__2_2108_);
v_binderName_2109_ = lean_ctor_get(v_e_2106_, 0);
lean_inc(v_binderName_2109_);
v_binderType_2110_ = lean_ctor_get(v_e_2106_, 1);
lean_inc_ref(v_binderType_2110_);
v_body_2111_ = lean_ctor_get(v_e_2106_, 2);
lean_inc_ref(v_body_2111_);
v_binderInfo_2112_ = lean_ctor_get_uint8(v_e_2106_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2106_, 3);
v___x_2113_ = lean_box(v_binderInfo_2112_);
v___x_2114_ = lean_apply_4(v_h__1_2107_, v_binderName_2109_, v_binderType_2110_, v_body_2111_, v___x_2113_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; 
lean_dec(v_h__1_2107_);
v___x_2115_ = lean_apply_2(v_h__2_2108_, v_e_2106_, lean_box(0));
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter(lean_object* v_motive_2116_, lean_object* v_e_2117_, lean_object* v_h__1_2118_, lean_object* v_h__2_2119_){
_start:
{
if (lean_obj_tag(v_e_2117_) == 7)
{
lean_object* v_binderName_2120_; lean_object* v_binderType_2121_; lean_object* v_body_2122_; uint8_t v_binderInfo_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec(v_h__2_2119_);
v_binderName_2120_ = lean_ctor_get(v_e_2117_, 0);
lean_inc(v_binderName_2120_);
v_binderType_2121_ = lean_ctor_get(v_e_2117_, 1);
lean_inc_ref(v_binderType_2121_);
v_body_2122_ = lean_ctor_get(v_e_2117_, 2);
lean_inc_ref(v_body_2122_);
v_binderInfo_2123_ = lean_ctor_get_uint8(v_e_2117_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2117_, 3);
v___x_2124_ = lean_box(v_binderInfo_2123_);
v___x_2125_ = lean_apply_4(v_h__1_2118_, v_binderName_2120_, v_binderType_2121_, v_body_2122_, v___x_2124_);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; 
lean_dec(v_h__1_2118_);
v___x_2126_ = lean_apply_2(v_h__2_2119_, v_e_2117_, lean_box(0));
return v___x_2126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object* v_type_2127_, lean_object* v_ps_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2128_, v___x_2132_, v_type_2127_, v_a_2129_, v_a_2130_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object* v_type_2134_, lean_object* v_ps_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_2134_, v_ps_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec_ref(v_ps_2135_);
return v_res_2139_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object* v_type_2140_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_Expr_headBeta(v_type_2140_);
switch(lean_obj_tag(v___x_2141_))
{
case 3:
{
lean_object* v_u_2142_; 
v_u_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_u_2142_);
lean_dec_ref_known(v___x_2141_, 1);
if (lean_obj_tag(v_u_2142_) == 0)
{
uint8_t v___x_2143_; 
v___x_2143_ = 1;
return v___x_2143_;
}
else
{
uint8_t v___x_2144_; 
lean_dec(v_u_2142_);
v___x_2144_ = 0;
return v___x_2144_;
}
}
case 7:
{
lean_object* v_body_2145_; 
v_body_2145_ = lean_ctor_get(v___x_2141_, 2);
lean_inc_ref(v_body_2145_);
lean_dec_ref_known(v___x_2141_, 3);
v_type_2140_ = v_body_2145_;
goto _start;
}
default: 
{
uint8_t v___x_2147_; 
lean_dec_ref(v___x_2141_);
v___x_2147_ = 0;
return v___x_2147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPredicateType___boxed(lean_object* v_type_2148_){
_start:
{
uint8_t v_res_2149_; lean_object* v_r_2150_; 
v_res_2149_ = l_Lean_Compiler_LCNF_isPredicateType(v_type_2148_);
v_r_2150_ = lean_box(v_res_2149_);
return v_r_2150_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_maybeTypeFormerType(lean_object* v_type_2151_){
_start:
{
lean_object* v___x_2152_; 
lean_inc_ref(v_type_2151_);
v___x_2152_ = l_Lean_Expr_headBeta(v_type_2151_);
switch(lean_obj_tag(v___x_2152_))
{
case 3:
{
uint8_t v___x_2153_; 
lean_dec_ref_known(v___x_2152_, 1);
lean_dec_ref(v_type_2151_);
v___x_2153_ = 1;
return v___x_2153_;
}
case 7:
{
lean_object* v_body_2154_; 
lean_dec_ref(v_type_2151_);
v_body_2154_ = lean_ctor_get(v___x_2152_, 2);
lean_inc_ref(v_body_2154_);
lean_dec_ref_known(v___x_2152_, 3);
v_type_2151_ = v_body_2154_;
goto _start;
}
default: 
{
uint8_t v___x_2156_; 
lean_dec_ref(v___x_2152_);
v___x_2156_ = l_Lean_Expr_isErased(v_type_2151_);
lean_dec_ref(v_type_2151_);
return v___x_2156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_maybeTypeFormerType___boxed(lean_object* v_type_2157_){
_start:
{
uint8_t v_res_2158_; lean_object* v_r_2159_; 
v_res_2158_ = l_Lean_Compiler_LCNF_maybeTypeFormerType(v_type_2157_);
v_r_2159_ = lean_box(v_res_2158_);
return v_r_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object* v_type_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Expr_getAppFn(v_type_2160_);
if (lean_obj_tag(v___x_2163_) == 4)
{
lean_object* v_declName_2164_; lean_object* v___x_2165_; lean_object* v_env_2166_; uint8_t v___x_2167_; 
v_declName_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_declName_2164_);
lean_dec_ref_known(v___x_2163_, 2);
v___x_2165_ = lean_st_ref_get(v_a_2161_);
v_env_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc_ref(v_env_2166_);
lean_dec(v___x_2165_);
v___x_2167_ = l_Lean_isClass(v_env_2166_, v_declName_2164_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec(v_declName_2164_);
v___x_2168_ = lean_box(0);
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2170_, 0, v_declName_2164_);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
return v___x_2171_;
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref(v___x_2163_);
v___x_2172_ = lean_box(0);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg___boxed(lean_object* v_type_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2174_, v_a_2175_);
lean_dec(v_a_2175_);
lean_dec_ref(v_type_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object* v_type_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2178_, v_a_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___boxed(lean_object* v_type_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Compiler_LCNF_isClass_x3f(v_type_2183_, v_a_2184_, v_a_2185_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
lean_dec_ref(v_type_2183_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object* v_type_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v___x_2191_; 
lean_inc_ref(v_type_2188_);
v___x_2191_ = l_Lean_Expr_headBeta(v_type_2188_);
if (lean_obj_tag(v___x_2191_) == 7)
{
lean_object* v_body_2192_; 
lean_dec_ref(v_type_2188_);
v_body_2192_ = lean_ctor_get(v___x_2191_, 2);
lean_inc_ref(v_body_2192_);
lean_dec_ref_known(v___x_2191_, 3);
v_type_2188_ = v_body_2192_;
goto _start;
}
else
{
lean_object* v___x_2194_; 
lean_dec_ref(v___x_2191_);
v___x_2194_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2188_, v_a_2189_);
lean_dec_ref(v_type_2188_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg___boxed(lean_object* v_type_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2195_, v_a_2196_);
lean_dec(v_a_2196_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object* v_type_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2199_, v_a_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___boxed(lean_object* v_type_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Compiler_LCNF_isArrowClass_x3f(v_type_2204_, v_a_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object* v_e_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_Expr_headBeta(v_e_2209_);
if (lean_obj_tag(v___x_2210_) == 7)
{
lean_object* v_body_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_body_2211_ = lean_ctor_get(v___x_2210_, 2);
lean_inc_ref(v_body_2211_);
lean_dec_ref_known(v___x_2210_, 3);
v___x_2212_ = l_Lean_Compiler_LCNF_getArrowArity(v_body_2211_);
v___x_2213_ = lean_unsigned_to_nat(1u);
v___x_2214_ = lean_nat_add(v___x_2212_, v___x_2213_);
lean_dec(v___x_2212_);
return v___x_2214_;
}
else
{
lean_object* v___x_2215_; 
lean_dec_ref(v___x_2210_);
v___x_2215_ = lean_unsigned_to_nat(0u);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object* v_type_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_Expr_getAppFn(v_type_2216_);
if (lean_obj_tag(v___x_2223_) == 4)
{
lean_object* v_declName_2224_; lean_object* v___x_2225_; lean_object* v_env_2226_; uint8_t v___x_2227_; lean_object* v___x_2228_; 
v_declName_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_declName_2224_);
lean_dec_ref_known(v___x_2223_, 2);
v___x_2225_ = lean_st_ref_get(v_a_2217_);
v_env_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc_ref(v_env_2226_);
lean_dec(v___x_2225_);
v___x_2227_ = 0;
v___x_2228_ = l_Lean_Environment_find_x3f(v_env_2226_, v_declName_2224_, v___x_2227_);
if (lean_obj_tag(v___x_2228_) == 1)
{
lean_object* v_val_2229_; 
v_val_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v___x_2228_, 1);
if (lean_obj_tag(v_val_2229_) == 5)
{
lean_object* v_val_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2241_; 
v_val_2230_ = lean_ctor_get(v_val_2229_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_val_2229_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2232_ = v_val_2229_;
v_isShared_2233_ = v_isSharedCheck_2241_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_val_2230_);
lean_dec(v_val_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2241_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2234_ = l_Lean_InductiveVal_numCtors(v_val_2230_);
lean_dec_ref(v_val_2230_);
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = lean_nat_dec_eq(v___x_2234_, v___x_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(v___x_2236_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2237_);
v___x_2239_ = v___x_2232_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_dec(v_val_2229_);
goto v___jp_2219_;
}
}
else
{
lean_dec(v___x_2228_);
goto v___jp_2219_;
}
}
else
{
uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_dec_ref(v___x_2223_);
v___x_2242_ = 0;
v___x_2243_ = lean_box(v___x_2242_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
v___jp_2219_:
{
uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = 0;
v___x_2221_ = lean_box(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg___boxed(lean_object* v_type_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2245_, v_a_2246_);
lean_dec(v_a_2246_);
lean_dec_ref(v_type_2245_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object* v_type_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2249_, v_a_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___boxed(lean_object* v_type_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors(v_type_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec_ref(v_type_2254_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object* v_n_2260_){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2262_ = l_Lean_Name_str___override(v_n_2260_, v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isBoxedName(lean_object* v_name_2263_){
_start:
{
if (lean_obj_tag(v_name_2263_) == 1)
{
lean_object* v_str_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v_str_2264_ = lean_ctor_get(v_name_2263_, 1);
v___x_2265_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2266_ = lean_string_dec_eq(v_str_2264_, v___x_2265_);
return v___x_2266_;
}
else
{
uint8_t v___x_2267_; 
v___x_2267_ = 0;
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isBoxedName___boxed(lean_object* v_name_2268_){
_start:
{
uint8_t v_res_2269_; lean_object* v_r_2270_; 
v_res_2269_ = l_Lean_Compiler_LCNF_isBoxedName(v_name_2268_);
lean_dec(v_name_2268_);
v_r_2270_ = lean_box(v_res_2269_);
return v_r_2270_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_box(0);
v___x_2275_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__1));
v___x_2276_ = l_Lean_Expr_const___override(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float(void){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = lean_box(0);
v___x_2282_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__1));
v___x_2283_ = l_Lean_Expr_const___override(v___x_2282_, v___x_2281_);
return v___x_2283_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32(void){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2);
return v___x_2284_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_box(0);
v___x_2289_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1));
v___x_2290_ = l_Lean_Expr_const___override(v___x_2289_, v___x_2288_);
return v___x_2290_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8(void){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2);
return v___x_2291_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2295_ = lean_box(0);
v___x_2296_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1));
v___x_2297_ = l_Lean_Expr_const___override(v___x_2296_, v___x_2295_);
return v___x_2297_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16(void){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2);
return v___x_2298_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = lean_box(0);
v___x_2303_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1));
v___x_2304_ = l_Lean_Expr_const___override(v___x_2303_, v___x_2302_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32(void){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2);
return v___x_2305_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_box(0);
v___x_2310_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1));
v___x_2311_ = l_Lean_Expr_const___override(v___x_2310_, v___x_2309_);
return v___x_2311_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64(void){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2);
return v___x_2312_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_box(0);
v___x_2317_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__1));
v___x_2318_ = l_Lean_Expr_const___override(v___x_2317_, v___x_2316_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize(void){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_usize___closed__2, &l_Lean_Compiler_LCNF_ImpureType_usize___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = lean_box(0);
v___x_2321_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_2322_ = l_Lean_Expr_const___override(v___x_2321_, v___x_2320_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased(void){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_erased___closed__0, &l_Lean_Compiler_LCNF_ImpureType_erased___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2327_ = lean_box(0);
v___x_2328_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__1));
v___x_2329_ = l_Lean_Expr_const___override(v___x_2328_, v___x_2327_);
return v___x_2329_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object(void){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2330_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = lean_box(0);
v___x_2335_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1));
v___x_2336_ = l_Lean_Expr_const___override(v___x_2335_, v___x_2334_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject(void){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = lean_box(0);
v___x_2342_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1));
v___x_2343_ = l_Lean_Expr_const___override(v___x_2342_, v___x_2341_);
return v___x_2343_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged(void){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = lean_box(0);
v___x_2346_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_2347_ = l_Lean_Expr_const___override(v___x_2346_, v___x_2345_);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void(void){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_void___closed__0, &l_Lean_Compiler_LCNF_ImpureType_void___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0);
return v___x_2348_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object* v_x_2349_){
_start:
{
if (lean_obj_tag(v_x_2349_) == 4)
{
lean_object* v_declName_2350_; 
v_declName_2350_ = lean_ctor_get(v_x_2349_, 0);
if (lean_obj_tag(v_declName_2350_) == 1)
{
lean_object* v_pre_2351_; 
v_pre_2351_ = lean_ctor_get(v_declName_2350_, 0);
if (lean_obj_tag(v_pre_2351_) == 0)
{
lean_object* v_us_2352_; lean_object* v_str_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v_us_2352_ = lean_ctor_get(v_x_2349_, 1);
v_str_2353_ = lean_ctor_get(v_declName_2350_, 1);
v___x_2354_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2355_ = lean_string_dec_eq(v_str_2353_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2357_ = lean_string_dec_eq(v_str_2353_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2359_ = lean_string_dec_eq(v_str_2353_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2360_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2361_ = lean_string_dec_eq(v_str_2353_, v___x_2360_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0));
v___x_2363_ = lean_string_dec_eq(v_str_2353_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2365_ = lean_string_dec_eq(v_str_2353_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__0));
v___x_2367_ = lean_string_dec_eq(v_str_2353_, v___x_2366_);
if (v___x_2367_ == 0)
{
return v___x_2367_;
}
else
{
if (lean_obj_tag(v_us_2352_) == 0)
{
return v___x_2367_;
}
else
{
return v___x_2365_;
}
}
}
else
{
if (lean_obj_tag(v_us_2352_) == 0)
{
return v___x_2365_;
}
else
{
return v___x_2363_;
}
}
}
else
{
if (lean_obj_tag(v_us_2352_) == 0)
{
return v___x_2363_;
}
else
{
return v___x_2361_;
}
}
}
else
{
if (lean_obj_tag(v_us_2352_) == 0)
{
return v___x_2361_;
}
else
{
return v___x_2359_;
}
}
}
else
{
if (lean_obj_tag(v_us_2352_) == 0)
{
return v___x_2359_;
}
else
{
return v___x_2357_;
}
}
}
else
{
if (lean_obj_tag(v_us_2352_) == 0)
{
return v___x_2357_;
}
else
{
return v___x_2355_;
}
}
}
else
{
if (lean_obj_tag(v_us_2352_) == 0)
{
return v___x_2355_;
}
else
{
uint8_t v___x_2368_; 
v___x_2368_ = 0;
return v___x_2368_;
}
}
}
else
{
uint8_t v___x_2369_; 
v___x_2369_ = 0;
return v___x_2369_;
}
}
else
{
uint8_t v___x_2370_; 
v___x_2370_ = 0;
return v___x_2370_;
}
}
else
{
uint8_t v___x_2371_; 
v___x_2371_ = 0;
return v___x_2371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar___boxed(lean_object* v_x_2372_){
_start:
{
uint8_t v_res_2373_; lean_object* v_r_2374_; 
v_res_2373_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_x_2372_);
lean_dec_ref(v_x_2372_);
v_r_2374_ = lean_box(v_res_2373_);
return v_r_2374_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(lean_object* v_x_2375_){
_start:
{
if (lean_obj_tag(v_x_2375_) == 4)
{
lean_object* v_declName_2376_; 
v_declName_2376_ = lean_ctor_get(v_x_2375_, 0);
if (lean_obj_tag(v_declName_2376_) == 1)
{
lean_object* v_pre_2377_; 
v_pre_2377_ = lean_ctor_get(v_declName_2376_, 0);
if (lean_obj_tag(v_pre_2377_) == 0)
{
lean_object* v_us_2378_; lean_object* v_str_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v_us_2378_ = lean_ctor_get(v_x_2375_, 1);
v_str_2379_ = lean_ctor_get(v_declName_2376_, 1);
v___x_2380_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2381_ = lean_string_dec_eq(v_str_2379_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2383_ = lean_string_dec_eq(v_str_2379_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2385_ = lean_string_dec_eq(v_str_2379_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2387_ = lean_string_dec_eq(v_str_2379_, v___x_2386_);
if (v___x_2387_ == 0)
{
return v___x_2387_;
}
else
{
if (lean_obj_tag(v_us_2378_) == 0)
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
if (lean_obj_tag(v_us_2378_) == 0)
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
if (lean_obj_tag(v_us_2378_) == 0)
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
if (lean_obj_tag(v_us_2378_) == 0)
{
return v___x_2381_;
}
else
{
uint8_t v___x_2388_; 
v___x_2388_ = 0;
return v___x_2388_;
}
}
}
else
{
uint8_t v___x_2389_; 
v___x_2389_ = 0;
return v___x_2389_;
}
}
else
{
uint8_t v___x_2390_; 
v___x_2390_ = 0;
return v___x_2390_;
}
}
else
{
uint8_t v___x_2391_; 
v___x_2391_ = 0;
return v___x_2391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj___boxed(lean_object* v_x_2392_){
_start:
{
uint8_t v_res_2393_; lean_object* v_r_2394_; 
v_res_2393_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(v_x_2392_);
lean_dec_ref(v_x_2392_);
v_r_2394_ = lean_box(v_res_2393_);
return v_r_2394_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object* v_x_2395_){
_start:
{
if (lean_obj_tag(v_x_2395_) == 4)
{
lean_object* v_declName_2396_; 
v_declName_2396_ = lean_ctor_get(v_x_2395_, 0);
if (lean_obj_tag(v_declName_2396_) == 1)
{
lean_object* v_pre_2397_; 
v_pre_2397_ = lean_ctor_get(v_declName_2396_, 0);
if (lean_obj_tag(v_pre_2397_) == 0)
{
lean_object* v_us_2398_; lean_object* v_str_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
v_us_2398_ = lean_ctor_get(v_x_2395_, 1);
v_str_2399_ = lean_ctor_get(v_declName_2396_, 1);
v___x_2400_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2401_ = lean_string_dec_eq(v_str_2399_, v___x_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2403_ = lean_string_dec_eq(v_str_2399_, v___x_2402_);
if (v___x_2403_ == 0)
{
return v___x_2403_;
}
else
{
if (lean_obj_tag(v_us_2398_) == 0)
{
return v___x_2403_;
}
else
{
return v___x_2401_;
}
}
}
else
{
if (lean_obj_tag(v_us_2398_) == 0)
{
return v___x_2401_;
}
else
{
uint8_t v___x_2404_; 
v___x_2404_ = 0;
return v___x_2404_;
}
}
}
else
{
uint8_t v___x_2405_; 
v___x_2405_ = 0;
return v___x_2405_;
}
}
else
{
uint8_t v___x_2406_; 
v___x_2406_ = 0;
return v___x_2406_;
}
}
else
{
uint8_t v___x_2407_; 
v___x_2407_ = 0;
return v___x_2407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef___boxed(lean_object* v_x_2408_){
_start:
{
uint8_t v_res_2409_; lean_object* v_r_2410_; 
v_res_2409_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_x_2408_);
lean_dec_ref(v_x_2408_);
v_r_2410_ = lean_box(v_res_2409_);
return v_r_2410_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(lean_object* v_x_2411_){
_start:
{
if (lean_obj_tag(v_x_2411_) == 4)
{
lean_object* v_declName_2412_; 
v_declName_2412_ = lean_ctor_get(v_x_2411_, 0);
if (lean_obj_tag(v_declName_2412_) == 1)
{
lean_object* v_pre_2413_; 
v_pre_2413_ = lean_ctor_get(v_declName_2412_, 0);
if (lean_obj_tag(v_pre_2413_) == 0)
{
lean_object* v_us_2414_; lean_object* v_str_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v_us_2414_ = lean_ctor_get(v_x_2411_, 1);
v_str_2415_ = lean_ctor_get(v_declName_2412_, 1);
v___x_2416_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2417_ = lean_string_dec_eq(v_str_2415_, v___x_2416_);
if (v___x_2417_ == 0)
{
return v___x_2417_;
}
else
{
if (lean_obj_tag(v_us_2414_) == 0)
{
return v___x_2417_;
}
else
{
uint8_t v___x_2418_; 
v___x_2418_ = 0;
return v___x_2418_;
}
}
}
else
{
uint8_t v___x_2419_; 
v___x_2419_ = 0;
return v___x_2419_;
}
}
else
{
uint8_t v___x_2420_; 
v___x_2420_ = 0;
return v___x_2420_;
}
}
else
{
uint8_t v___x_2421_; 
v___x_2421_ = 0;
return v___x_2421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef___boxed(lean_object* v_x_2422_){
_start:
{
uint8_t v_res_2423_; lean_object* v_r_2424_; 
v_res_2423_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_x_2422_);
lean_dec_ref(v_x_2422_);
v_r_2424_ = lean_box(v_res_2423_);
return v_r_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object* v_x_2425_){
_start:
{
if (lean_obj_tag(v_x_2425_) == 4)
{
lean_object* v_declName_2432_; 
v_declName_2432_ = lean_ctor_get(v_x_2425_, 0);
if (lean_obj_tag(v_declName_2432_) == 1)
{
lean_object* v_pre_2433_; 
v_pre_2433_ = lean_ctor_get(v_declName_2432_, 0);
if (lean_obj_tag(v_pre_2433_) == 0)
{
lean_object* v_us_2434_; lean_object* v_str_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v_us_2434_ = lean_ctor_get(v_x_2425_, 1);
v_str_2435_ = lean_ctor_get(v_declName_2432_, 1);
v___x_2436_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2437_ = lean_string_dec_eq(v_str_2435_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2438_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2439_ = lean_string_dec_eq(v_str_2435_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2441_ = lean_string_dec_eq(v_str_2435_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; uint8_t v___x_2443_; 
v___x_2442_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2443_ = lean_string_dec_eq(v_str_2435_, v___x_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2445_ = lean_string_dec_eq(v_str_2435_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2446_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2447_ = lean_string_dec_eq(v_str_2435_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2449_ = lean_string_dec_eq(v_str_2435_, v___x_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2450_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2451_ = lean_string_dec_eq(v_str_2435_, v___x_2450_);
if (v___x_2451_ == 0)
{
goto v___jp_2426_;
}
else
{
if (lean_obj_tag(v_us_2434_) == 0)
{
goto v___jp_2430_;
}
else
{
goto v___jp_2426_;
}
}
}
else
{
if (lean_obj_tag(v_us_2434_) == 0)
{
goto v___jp_2430_;
}
else
{
goto v___jp_2426_;
}
}
}
else
{
if (lean_obj_tag(v_us_2434_) == 0)
{
goto v___jp_2430_;
}
else
{
goto v___jp_2426_;
}
}
}
else
{
if (lean_obj_tag(v_us_2434_) == 0)
{
goto v___jp_2430_;
}
else
{
goto v___jp_2426_;
}
}
}
else
{
if (lean_obj_tag(v_us_2434_) == 0)
{
goto v___jp_2428_;
}
else
{
goto v___jp_2426_;
}
}
}
else
{
if (lean_obj_tag(v_us_2434_) == 0)
{
goto v___jp_2428_;
}
else
{
goto v___jp_2426_;
}
}
}
else
{
if (lean_obj_tag(v_us_2434_) == 0)
{
goto v___jp_2428_;
}
else
{
goto v___jp_2426_;
}
}
}
else
{
if (lean_obj_tag(v_us_2434_) == 0)
{
goto v___jp_2428_;
}
else
{
goto v___jp_2426_;
}
}
}
else
{
goto v___jp_2426_;
}
}
else
{
goto v___jp_2426_;
}
}
else
{
goto v___jp_2426_;
}
v___jp_2426_:
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2427_;
}
v___jp_2428_:
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2429_;
}
v___jp_2430_:
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed___boxed(lean_object* v_x_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_x_2452_);
lean_dec_ref(v_x_2452_);
return v_res_2453_;
}
}
lean_object* runtime_initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
