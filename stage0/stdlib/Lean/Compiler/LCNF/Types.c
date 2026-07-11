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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0;
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
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static uint64_t _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0(void){
_start:
{
uint8_t v___x_318_; uint64_t v___x_319_; 
v___x_318_ = 0;
v___x_319_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(lean_object* v_type_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; uint8_t v_foApprox_327_; uint8_t v_ctxApprox_328_; uint8_t v_quasiPatternApprox_329_; uint8_t v_constApprox_330_; uint8_t v_isDefEqStuckEx_331_; uint8_t v_unificationHints_332_; uint8_t v_proofIrrelevance_333_; uint8_t v_assignSyntheticOpaque_334_; uint8_t v_offsetCnstrs_335_; uint8_t v_etaStruct_336_; uint8_t v_univApprox_337_; uint8_t v_iota_338_; uint8_t v_beta_339_; uint8_t v_proj_340_; uint8_t v_zeta_341_; uint8_t v_zetaDelta_342_; uint8_t v_zetaUnused_343_; uint8_t v_zetaHave_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_376_; 
v___x_326_ = l_Lean_Meta_Context_config(v_a_321_);
v_foApprox_327_ = lean_ctor_get_uint8(v___x_326_, 0);
v_ctxApprox_328_ = lean_ctor_get_uint8(v___x_326_, 1);
v_quasiPatternApprox_329_ = lean_ctor_get_uint8(v___x_326_, 2);
v_constApprox_330_ = lean_ctor_get_uint8(v___x_326_, 3);
v_isDefEqStuckEx_331_ = lean_ctor_get_uint8(v___x_326_, 4);
v_unificationHints_332_ = lean_ctor_get_uint8(v___x_326_, 5);
v_proofIrrelevance_333_ = lean_ctor_get_uint8(v___x_326_, 6);
v_assignSyntheticOpaque_334_ = lean_ctor_get_uint8(v___x_326_, 7);
v_offsetCnstrs_335_ = lean_ctor_get_uint8(v___x_326_, 8);
v_etaStruct_336_ = lean_ctor_get_uint8(v___x_326_, 10);
v_univApprox_337_ = lean_ctor_get_uint8(v___x_326_, 11);
v_iota_338_ = lean_ctor_get_uint8(v___x_326_, 12);
v_beta_339_ = lean_ctor_get_uint8(v___x_326_, 13);
v_proj_340_ = lean_ctor_get_uint8(v___x_326_, 14);
v_zeta_341_ = lean_ctor_get_uint8(v___x_326_, 15);
v_zetaDelta_342_ = lean_ctor_get_uint8(v___x_326_, 16);
v_zetaUnused_343_ = lean_ctor_get_uint8(v___x_326_, 17);
v_zetaHave_344_ = lean_ctor_get_uint8(v___x_326_, 18);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_376_ == 0)
{
v___x_346_ = v___x_326_;
v_isShared_347_ = v_isSharedCheck_376_;
goto v_resetjp_345_;
}
else
{
lean_dec(v___x_326_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_376_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
uint8_t v_trackZetaDelta_348_; lean_object* v_zetaDeltaSet_349_; lean_object* v_lctx_350_; lean_object* v_localInstances_351_; lean_object* v_defEqCtx_x3f_352_; lean_object* v_synthPendingDepth_353_; lean_object* v_canUnfold_x3f_354_; uint8_t v_univApprox_355_; uint8_t v_inTypeClassResolution_356_; uint8_t v_cacheInferType_357_; uint8_t v___x_358_; lean_object* v_config_360_; 
v_trackZetaDelta_348_ = lean_ctor_get_uint8(v_a_321_, sizeof(void*)*7);
v_zetaDeltaSet_349_ = lean_ctor_get(v_a_321_, 1);
v_lctx_350_ = lean_ctor_get(v_a_321_, 2);
v_localInstances_351_ = lean_ctor_get(v_a_321_, 3);
v_defEqCtx_x3f_352_ = lean_ctor_get(v_a_321_, 4);
v_synthPendingDepth_353_ = lean_ctor_get(v_a_321_, 5);
v_canUnfold_x3f_354_ = lean_ctor_get(v_a_321_, 6);
v_univApprox_355_ = lean_ctor_get_uint8(v_a_321_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_356_ = lean_ctor_get_uint8(v_a_321_, sizeof(void*)*7 + 2);
v_cacheInferType_357_ = lean_ctor_get_uint8(v_a_321_, sizeof(void*)*7 + 3);
v___x_358_ = 0;
if (v_isShared_347_ == 0)
{
v_config_360_ = v___x_346_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 0, v_foApprox_327_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 1, v_ctxApprox_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 2, v_quasiPatternApprox_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 3, v_constApprox_330_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 4, v_isDefEqStuckEx_331_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 5, v_unificationHints_332_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 6, v_proofIrrelevance_333_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 7, v_assignSyntheticOpaque_334_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 8, v_offsetCnstrs_335_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 10, v_etaStruct_336_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 11, v_univApprox_337_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 12, v_iota_338_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 13, v_beta_339_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 14, v_proj_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 15, v_zeta_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 16, v_zetaDelta_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 17, v_zetaUnused_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, 18, v_zetaHave_344_);
v_config_360_ = v_reuseFailAlloc_375_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
uint64_t v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v_key_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_ctor_set_uint8(v_config_360_, 9, v___x_358_);
v___x_361_ = l_Lean_Meta_Context_configKey(v_a_321_);
v___x_362_ = 3ULL;
v___x_363_ = lean_uint64_shift_right(v___x_361_, v___x_362_);
v___x_364_ = lean_uint64_shift_left(v___x_363_, v___x_362_);
v___x_365_ = lean_uint64_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0);
v_key_366_ = lean_uint64_lor(v___x_364_, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_367_, 0, v_config_360_);
lean_ctor_set_uint64(v___x_367_, sizeof(void*)*1, v_key_366_);
lean_inc(v_canUnfold_x3f_354_);
lean_inc(v_synthPendingDepth_353_);
lean_inc(v_defEqCtx_x3f_352_);
lean_inc_ref(v_localInstances_351_);
lean_inc_ref(v_lctx_350_);
lean_inc(v_zetaDeltaSet_349_);
v___x_368_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_zetaDeltaSet_349_);
lean_ctor_set(v___x_368_, 2, v_lctx_350_);
lean_ctor_set(v___x_368_, 3, v_localInstances_351_);
lean_ctor_set(v___x_368_, 4, v_defEqCtx_x3f_352_);
lean_ctor_set(v___x_368_, 5, v_synthPendingDepth_353_);
lean_ctor_set(v___x_368_, 6, v_canUnfold_x3f_354_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*7, v_trackZetaDelta_348_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*7 + 1, v_univApprox_355_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*7 + 2, v_inTypeClassResolution_356_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*7 + 3, v_cacheInferType_357_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
v___x_369_ = lean_whnf(v_type_320_, v___x_368_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_371_; uint8_t v___x_372_; uint8_t v___x_373_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc_n(v_a_370_, 2);
v___x_371_ = l_Lean_Expr_eta(v_a_370_);
v___x_372_ = lean_expr_eqv(v___x_371_, v_a_370_);
lean_dec(v_a_370_);
v___x_373_ = lean_bool_not(v___x_372_);
if (v___x_373_ == 0)
{
lean_dec_ref(v___x_371_);
return v___x_369_;
}
else
{
lean_dec_ref_known(v___x_369_, 1);
v_type_320_ = v___x_371_;
goto _start;
}
}
else
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___boxed(lean_object* v_type_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(lean_object* v_msgData_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v_env_391_; lean_object* v___x_392_; lean_object* v_mctx_393_; lean_object* v_lctx_394_; lean_object* v_options_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_390_ = lean_st_ref_get(v___y_388_);
v_env_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc_ref(v_env_391_);
lean_dec(v___x_390_);
v___x_392_ = lean_st_ref_get(v___y_386_);
v_mctx_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_mctx_393_);
lean_dec(v___x_392_);
v_lctx_394_ = lean_ctor_get(v___y_385_, 2);
v_options_395_ = lean_ctor_get(v___y_387_, 2);
lean_inc_ref(v_options_395_);
lean_inc_ref(v_lctx_394_);
v___x_396_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_396_, 0, v_env_391_);
lean_ctor_set(v___x_396_, 1, v_mctx_393_);
lean_ctor_set(v___x_396_, 2, v_lctx_394_);
lean_ctor_set(v___x_396_, 3, v_options_395_);
v___x_397_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_msgData_384_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6___boxed(lean_object* v_msgData_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msgData_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(lean_object* v_msg_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_ref_412_; lean_object* v___x_413_; lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_422_; 
v_ref_412_ = lean_ctor_get(v___y_409_, 5);
v___x_413_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msg_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_422_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
lean_inc(v_ref_412_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v_ref_412_);
lean_ctor_set(v___x_418_, 1, v_a_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 1);
lean_ctor_set(v___x_416_, 0, v___x_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg___boxed(lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(lean_object* v_ref_430_, lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_fileName_437_; lean_object* v_fileMap_438_; lean_object* v_options_439_; lean_object* v_currRecDepth_440_; lean_object* v_maxRecDepth_441_; lean_object* v_ref_442_; lean_object* v_currNamespace_443_; lean_object* v_openDecls_444_; lean_object* v_initHeartbeats_445_; lean_object* v_maxHeartbeats_446_; lean_object* v_quotContext_447_; lean_object* v_currMacroScope_448_; uint8_t v_diag_449_; lean_object* v_cancelTk_x3f_450_; uint8_t v_suppressElabErrors_451_; lean_object* v_inheritedTraceOptions_452_; lean_object* v_ref_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_fileName_437_ = lean_ctor_get(v___y_434_, 0);
v_fileMap_438_ = lean_ctor_get(v___y_434_, 1);
v_options_439_ = lean_ctor_get(v___y_434_, 2);
v_currRecDepth_440_ = lean_ctor_get(v___y_434_, 3);
v_maxRecDepth_441_ = lean_ctor_get(v___y_434_, 4);
v_ref_442_ = lean_ctor_get(v___y_434_, 5);
v_currNamespace_443_ = lean_ctor_get(v___y_434_, 6);
v_openDecls_444_ = lean_ctor_get(v___y_434_, 7);
v_initHeartbeats_445_ = lean_ctor_get(v___y_434_, 8);
v_maxHeartbeats_446_ = lean_ctor_get(v___y_434_, 9);
v_quotContext_447_ = lean_ctor_get(v___y_434_, 10);
v_currMacroScope_448_ = lean_ctor_get(v___y_434_, 11);
v_diag_449_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*14);
v_cancelTk_x3f_450_ = lean_ctor_get(v___y_434_, 12);
v_suppressElabErrors_451_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_452_ = lean_ctor_get(v___y_434_, 13);
v_ref_453_ = l_Lean_replaceRef(v_ref_430_, v_ref_442_);
lean_inc_ref(v_inheritedTraceOptions_452_);
lean_inc(v_cancelTk_x3f_450_);
lean_inc(v_currMacroScope_448_);
lean_inc(v_quotContext_447_);
lean_inc(v_maxHeartbeats_446_);
lean_inc(v_initHeartbeats_445_);
lean_inc(v_openDecls_444_);
lean_inc(v_currNamespace_443_);
lean_inc(v_maxRecDepth_441_);
lean_inc(v_currRecDepth_440_);
lean_inc_ref(v_options_439_);
lean_inc_ref(v_fileMap_438_);
lean_inc_ref(v_fileName_437_);
v___x_454_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_454_, 0, v_fileName_437_);
lean_ctor_set(v___x_454_, 1, v_fileMap_438_);
lean_ctor_set(v___x_454_, 2, v_options_439_);
lean_ctor_set(v___x_454_, 3, v_currRecDepth_440_);
lean_ctor_set(v___x_454_, 4, v_maxRecDepth_441_);
lean_ctor_set(v___x_454_, 5, v_ref_453_);
lean_ctor_set(v___x_454_, 6, v_currNamespace_443_);
lean_ctor_set(v___x_454_, 7, v_openDecls_444_);
lean_ctor_set(v___x_454_, 8, v_initHeartbeats_445_);
lean_ctor_set(v___x_454_, 9, v_maxHeartbeats_446_);
lean_ctor_set(v___x_454_, 10, v_quotContext_447_);
lean_ctor_set(v___x_454_, 11, v_currMacroScope_448_);
lean_ctor_set(v___x_454_, 12, v_cancelTk_x3f_450_);
lean_ctor_set(v___x_454_, 13, v_inheritedTraceOptions_452_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*14, v_diag_449_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*14 + 1, v_suppressElabErrors_451_);
v___x_455_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_431_, v___y_432_, v___y_433_, v___x_454_, v___y_435_);
lean_dec_ref_known(v___x_454_, 14);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg___boxed(lean_object* v_ref_456_, lean_object* v_msg_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_456_, v_msg_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v_ref_456_);
return v_res_463_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_464_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
lean_ctor_set(v___x_469_, 2, v___x_468_);
lean_ctor_set(v___x_469_, 3, v___x_468_);
lean_ctor_set(v___x_469_, 4, v___x_467_);
lean_ctor_set(v___x_469_, 5, v___x_467_);
lean_ctor_set(v___x_469_, 6, v___x_467_);
lean_ctor_set(v___x_469_, 7, v___x_467_);
lean_ctor_set(v___x_469_, 8, v___x_467_);
lean_ctor_set(v___x_469_, 9, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_unsigned_to_nat(32u);
v___x_471_ = lean_mk_empty_array_with_capacity(v___x_470_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_473_ = ((size_t)5ULL);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_unsigned_to_nat(32u);
v___x_476_ = lean_mk_empty_array_with_capacity(v___x_475_);
v___x_477_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_478_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_476_);
lean_ctor_set(v___x_478_, 2, v___x_474_);
lean_ctor_set(v___x_478_, 3, v___x_474_);
lean_ctor_set_usize(v___x_478_, 4, v___x_473_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_479_ = lean_box(1);
v___x_480_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_481_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_480_);
lean_ctor_set(v___x_482_, 2, v___x_479_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_500_ = l_Lean_stringToMessageData(v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_503_ = l_Lean_stringToMessageData(v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_504_, lean_object* v_declHint_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; lean_object* v_env_509_; uint8_t v___y_511_; uint8_t v___x_567_; uint8_t v___x_568_; 
v___x_508_ = lean_st_ref_get(v___y_506_);
v_env_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc_ref(v_env_509_);
lean_dec(v___x_508_);
v___x_567_ = l_Lean_Name_isAnonymous(v_declHint_505_);
v___x_568_ = lean_bool_not(v___x_567_);
if (v___x_568_ == 0)
{
v___y_511_ = v___x_568_;
goto v___jp_510_;
}
else
{
uint8_t v_isExporting_569_; 
v_isExporting_569_ = lean_ctor_get_uint8(v_env_509_, sizeof(void*)*8);
v___y_511_ = v_isExporting_569_;
goto v___jp_510_;
}
v___jp_510_:
{
if (v___y_511_ == 0)
{
lean_object* v___x_512_; 
lean_dec_ref(v_env_509_);
lean_dec(v_declHint_505_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v_msg_504_);
return v___x_512_;
}
else
{
uint8_t v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_513_ = 0;
lean_inc_ref(v_env_509_);
v___x_514_ = l_Lean_Environment_setExporting(v_env_509_, v___x_513_);
lean_inc(v_declHint_505_);
lean_inc_ref(v___x_514_);
v___x_515_ = l_Lean_Environment_contains(v___x_514_, v_declHint_505_, v___y_511_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
lean_dec_ref(v___x_514_);
lean_dec_ref(v_env_509_);
lean_dec(v_declHint_505_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_msg_504_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_c_522_; lean_object* v___x_523_; 
v___x_517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_519_ = l_Lean_Options_empty;
v___x_520_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_520_, 0, v___x_514_);
lean_ctor_set(v___x_520_, 1, v___x_517_);
lean_ctor_set(v___x_520_, 2, v___x_518_);
lean_ctor_set(v___x_520_, 3, v___x_519_);
lean_inc(v_declHint_505_);
v___x_521_ = l_Lean_MessageData_ofConstName(v_declHint_505_, v___x_513_);
v_c_522_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_522_, 0, v___x_520_);
lean_ctor_set(v_c_522_, 1, v___x_521_);
v___x_523_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_509_, v_declHint_505_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec_ref(v_env_509_);
lean_dec(v_declHint_505_);
v___x_524_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v_c_522_);
v___x_526_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_MessageData_note(v___x_527_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v_msg_504_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v_val_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_566_; 
v_val_531_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_566_ == 0)
{
v___x_533_ = v___x_523_;
v_isShared_534_ = v_isSharedCheck_566_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_val_531_);
lean_dec(v___x_523_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_566_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_mod_538_; uint8_t v___x_539_; 
v___x_535_ = lean_box(0);
v___x_536_ = l_Lean_Environment_header(v_env_509_);
lean_dec_ref(v_env_509_);
v___x_537_ = l_Lean_EnvironmentHeader_moduleNames(v___x_536_);
v_mod_538_ = lean_array_get(v___x_535_, v___x_537_, v_val_531_);
lean_dec(v_val_531_);
lean_dec_ref(v___x_537_);
v___x_539_ = l_Lean_isPrivateName(v_declHint_505_);
lean_dec(v_declHint_505_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_540_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v_c_522_);
v___x_542_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_MessageData_ofName(v_mod_538_);
v___x_545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = l_Lean_MessageData_note(v___x_547_);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v_msg_504_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 0);
lean_ctor_set(v___x_533_, 0, v___x_549_);
v___x_551_ = v___x_533_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_553_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_c_522_);
v___x_555_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_Lean_MessageData_ofName(v_mod_538_);
v___x_558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = l_Lean_MessageData_note(v___x_560_);
v___x_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_562_, 0, v_msg_504_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 0);
lean_ctor_set(v___x_533_, 0, v___x_562_);
v___x_564_ = v___x_533_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_570_, lean_object* v_declHint_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_570_, v_declHint_571_, v___y_572_);
lean_dec(v___y_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(lean_object* v_msg_575_, lean_object* v_declHint_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_592_; 
v___x_582_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_575_, v_declHint_576_, v___y_580_);
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_592_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_592_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_592_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_587_ = l_Lean_unknownIdentifierMessageTag;
v___x_588_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_a_583_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_588_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9___boxed(lean_object* v_msg_593_, lean_object* v_declHint_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_593_, v_declHint_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(lean_object* v_ref_601_, lean_object* v_msg_602_, lean_object* v_declHint_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; lean_object* v_a_610_; lean_object* v___x_611_; 
v___x_609_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_602_, v_declHint_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref(v___x_609_);
v___x_611_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_601_, v_a_610_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_ref_612_, lean_object* v_msg_613_, lean_object* v_declHint_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_612_, v_msg_613_, v_declHint_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v_ref_612_);
return v_res_620_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0));
v___x_623_ = l_Lean_stringToMessageData(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2));
v___x_626_ = l_Lean_stringToMessageData(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(lean_object* v_ref_627_, lean_object* v_constName_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_634_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1);
v___x_635_ = 0;
lean_inc(v_constName_628_);
v___x_636_ = l_Lean_MessageData_ofConstName(v_constName_628_, v___x_635_);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_634_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_627_, v___x_639_, v_constName_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___boxed(lean_object* v_ref_641_, lean_object* v_constName_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_641_, v_constName_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v_ref_641_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(lean_object* v_constName_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_ref_655_; lean_object* v___x_656_; 
v_ref_655_ = lean_ctor_get(v___y_652_, 5);
v___x_656_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_655_, v_constName_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg___boxed(lean_object* v_constName_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(lean_object* v_constName_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v_env_671_; uint8_t v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_st_ref_get(v___y_668_);
v_env_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc_ref(v_env_671_);
lean_dec(v___x_670_);
v___x_672_ = 0;
lean_inc(v_constName_664_);
v___x_673_ = l_Lean_Environment_find_x3f(v_env_671_, v_constName_664_, v___x_672_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_674_;
}
else
{
lean_object* v_val_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec(v_constName_664_);
v_val_675_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_673_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_val_675_);
lean_dec(v___x_673_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set_tag(v___x_677_, 0);
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_val_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4___boxed(lean_object* v_constName_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_constName_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(lean_object* v_binderType_690_, lean_object* v_body_691_, lean_object* v_binderName_692_, uint8_t v_binderInfo_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_binderType_690_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = lean_expr_instantiate1(v_body_691_, v_x_694_);
v___x_703_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_702_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; uint8_t v___x_705_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
v___x_705_ = l_Lean_Expr_isErased(v_a_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_717_; 
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; 
v_unused_718_ = lean_ctor_get(v___x_703_, 0);
lean_dec(v_unused_718_);
v___x_707_ = v___x_703_;
v_isShared_708_ = v_isSharedCheck_717_;
goto v_resetjp_706_;
}
else
{
lean_dec(v___x_703_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_717_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_709_ = lean_unsigned_to_nat(1u);
v___x_710_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___x_711_ = lean_array_push(v___x_710_, v_x_694_);
v___x_712_ = lean_expr_abstract(v_a_704_, v___x_711_);
lean_dec_ref(v___x_711_);
lean_dec(v_a_704_);
v___x_713_ = l_Lean_Expr_lam___override(v_binderName_692_, v_a_701_, v___x_712_, v_binderInfo_693_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_713_);
v___x_715_ = v___x_707_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
else
{
lean_dec(v_a_704_);
lean_dec(v_a_701_);
lean_dec_ref(v_x_694_);
lean_dec(v_binderName_692_);
return v___x_703_;
}
}
else
{
lean_dec(v_a_701_);
lean_dec_ref(v_x_694_);
lean_dec(v_binderName_692_);
return v___x_703_;
}
}
else
{
lean_dec_ref(v_x_694_);
lean_dec(v_binderName_692_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed(lean_object* v_binderType_719_, lean_object* v_body_720_, lean_object* v_binderName_721_, lean_object* v_binderInfo_722_, lean_object* v_x_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
uint8_t v_binderInfo_9721__boxed_729_; lean_object* v_res_730_; 
v_binderInfo_9721__boxed_729_ = lean_unbox(v_binderInfo_722_);
v_res_730_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(v_binderType_719_, v_body_720_, v_binderName_721_, v_binderInfo_9721__boxed_729_, v_x_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec_ref(v_body_720_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(lean_object* v_d_731_, lean_object* v_xs_732_, lean_object* v_body_733_, lean_object* v_binderName_734_, uint8_t v_binderInfo_735_, lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v_isBorrowed_742_; lean_object* v___x_743_; 
v_isBorrowed_742_ = l_Lean_isMarkedBorrowed(v_d_731_);
v___x_743_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_d_731_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v_d_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___x_762_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v___x_762_ = lean_expr_abstract(v_a_744_, v_xs_732_);
lean_dec(v_a_744_);
if (v_isBorrowed_742_ == 0)
{
v_d_746_ = v___x_762_;
v___y_747_ = v___y_737_;
v___y_748_ = v___y_738_;
v___y_749_ = v___y_739_;
v___y_750_ = v___y_740_;
goto v___jp_745_;
}
else
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_markBorrowed(v___x_762_);
v_d_746_ = v___x_763_;
v___y_747_ = v___y_737_;
v___y_748_ = v___y_738_;
v___y_749_ = v___y_739_;
v___y_750_ = v___y_740_;
goto v___jp_745_;
}
v___jp_745_:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_array_push(v_xs_732_, v_x_736_);
v___x_752_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_body_733_, v___x_751_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_761_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = l_Lean_Expr_forallE___override(v_binderName_734_, v_d_746_, v_a_753_, v_binderInfo_735_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
lean_dec_ref(v_d_746_);
lean_dec(v_binderName_734_);
return v___x_752_;
}
}
}
else
{
lean_dec_ref(v_x_736_);
lean_dec(v_binderName_734_);
lean_dec_ref(v_body_733_);
lean_dec_ref(v_xs_732_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed(lean_object* v_d_764_, lean_object* v_xs_765_, lean_object* v_body_766_, lean_object* v_binderName_767_, lean_object* v_binderInfo_768_, lean_object* v_x_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
uint8_t v_binderInfo_9743__boxed_775_; lean_object* v_res_776_; 
v_binderInfo_9743__boxed_775_ = lean_unbox(v_binderInfo_768_);
v_res_776_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(v_d_764_, v_xs_765_, v_body_766_, v_binderName_767_, v_binderInfo_9743__boxed_775_, v_x_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(lean_object* v_e_777_, lean_object* v_xs_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
if (lean_obj_tag(v_e_777_) == 7)
{
lean_object* v_binderName_784_; lean_object* v_binderType_785_; lean_object* v_body_786_; uint8_t v_binderInfo_787_; lean_object* v_d_788_; lean_object* v___x_789_; lean_object* v___f_790_; uint8_t v___x_791_; lean_object* v___x_792_; 
v_binderName_784_ = lean_ctor_get(v_e_777_, 0);
lean_inc_n(v_binderName_784_, 2);
v_binderType_785_ = lean_ctor_get(v_e_777_, 1);
lean_inc_ref(v_binderType_785_);
v_body_786_ = lean_ctor_get(v_e_777_, 2);
lean_inc_ref(v_body_786_);
v_binderInfo_787_ = lean_ctor_get_uint8(v_e_777_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_777_, 3);
v_d_788_ = lean_expr_instantiate_rev(v_binderType_785_, v_xs_778_);
lean_dec_ref(v_binderType_785_);
v___x_789_ = lean_box(v_binderInfo_787_);
lean_inc_ref(v_d_788_);
v___f_790_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed), 11, 5);
lean_closure_set(v___f_790_, 0, v_d_788_);
lean_closure_set(v___f_790_, 1, v_xs_778_);
lean_closure_set(v___f_790_, 2, v_body_786_);
lean_closure_set(v___f_790_, 3, v_binderName_784_);
lean_closure_set(v___f_790_, 4, v___x_789_);
v___x_791_ = 0;
v___x_792_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_784_, v_binderInfo_787_, v_d_788_, v___f_790_, v___x_791_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
return v___x_792_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_expr_instantiate_rev(v_e_777_, v_xs_778_);
lean_dec_ref(v_e_777_);
v___x_794_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_793_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_803_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_803_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_expr_abstract(v_a_795_, v_xs_778_);
lean_dec_ref(v_xs_778_);
lean_dec(v_a_795_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_799_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
else
{
lean_dec_ref(v_xs_778_);
return v___x_794_;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0(void){
_start:
{
lean_object* v___x_804_; lean_object* v_dummy_805_; 
v___x_804_ = lean_box(0);
v_dummy_805_ = l_Lean_Expr_sort___override(v___x_804_);
return v_dummy_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(lean_object* v_type_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; 
lean_inc_ref(v_type_809_);
v___x_815_ = l_Lean_Meta_isProp(v_type_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_882_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_882_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_882_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_882_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
uint8_t v___x_820_; 
v___x_820_ = lean_unbox(v_a_816_);
lean_dec(v_a_816_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
v___x_821_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
switch(lean_obj_tag(v_a_822_))
{
case 3:
{
lean_dec_ref_known(v_a_822_, 1);
lean_del_object(v___x_818_);
return v___x_821_;
}
case 4:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec_ref_known(v___x_821_, 1);
lean_del_object(v___x_818_);
v___x_828_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_829_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_822_, v___x_828_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_829_;
}
case 6:
{
lean_object* v_binderName_830_; lean_object* v_binderType_831_; lean_object* v_body_832_; uint8_t v_binderInfo_833_; lean_object* v___x_834_; lean_object* v___f_835_; uint8_t v___x_836_; lean_object* v___x_837_; 
lean_dec_ref_known(v___x_821_, 1);
lean_del_object(v___x_818_);
v_binderName_830_ = lean_ctor_get(v_a_822_, 0);
lean_inc_n(v_binderName_830_, 2);
v_binderType_831_ = lean_ctor_get(v_a_822_, 1);
lean_inc_ref_n(v_binderType_831_, 2);
v_body_832_ = lean_ctor_get(v_a_822_, 2);
lean_inc_ref(v_body_832_);
v_binderInfo_833_ = lean_ctor_get_uint8(v_a_822_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_822_, 3);
v___x_834_ = lean_box(v_binderInfo_833_);
v___f_835_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_835_, 0, v_binderType_831_);
lean_closure_set(v___f_835_, 1, v_body_832_);
lean_closure_set(v___f_835_, 2, v_binderName_830_);
lean_closure_set(v___f_835_, 3, v___x_834_);
v___x_836_ = 0;
v___x_837_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_830_, v_binderInfo_833_, v_binderType_831_, v___f_835_, v___x_836_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_837_;
}
case 7:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref_known(v___x_821_, 1);
lean_del_object(v___x_818_);
v___x_838_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_839_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_a_822_, v___x_838_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_839_;
}
case 5:
{
lean_object* v_dummy_840_; lean_object* v_nargs_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref_known(v___x_821_, 1);
lean_del_object(v___x_818_);
v_dummy_840_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0);
v_nargs_841_ = l_Lean_Expr_getAppNumArgs(v_a_822_);
lean_inc(v_nargs_841_);
v___x_842_ = lean_mk_array(v_nargs_841_, v_dummy_840_);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_sub(v_nargs_841_, v___x_843_);
lean_dec(v_nargs_841_);
v___x_845_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_a_822_, v___x_842_, v___x_844_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_845_;
}
case 1:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref_known(v___x_821_, 1);
lean_del_object(v___x_818_);
v___x_846_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_847_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_822_, v___x_846_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_847_;
}
case 11:
{
lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_876_; 
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; 
v_unused_877_ = lean_ctor_get(v___x_821_, 0);
lean_dec(v_unused_877_);
v___x_849_ = v___x_821_;
v_isShared_850_ = v_isSharedCheck_876_;
goto v_resetjp_848_;
}
else
{
lean_dec(v___x_821_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_876_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_typeName_851_; 
v_typeName_851_ = lean_ctor_get(v_a_822_, 0);
lean_inc(v_typeName_851_);
if (lean_obj_tag(v_typeName_851_) == 1)
{
lean_object* v_pre_852_; 
v_pre_852_ = lean_ctor_get(v_typeName_851_, 0);
if (lean_obj_tag(v_pre_852_) == 0)
{
lean_object* v_idx_853_; lean_object* v_struct_854_; lean_object* v_str_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_idx_853_ = lean_ctor_get(v_a_822_, 1);
lean_inc(v_idx_853_);
v_struct_854_ = lean_ctor_get(v_a_822_, 2);
lean_inc_ref(v_struct_854_);
lean_dec_ref_known(v_a_822_, 3);
v_str_855_ = lean_ctor_get(v_typeName_851_, 1);
lean_inc_ref(v_str_855_);
lean_dec_ref_known(v_typeName_851_, 2);
v___x_856_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1));
v___x_857_ = lean_string_dec_eq(v_str_855_, v___x_856_);
lean_dec_ref(v_str_855_);
if (v___x_857_ == 0)
{
lean_dec_ref(v_struct_854_);
lean_dec(v_idx_853_);
lean_del_object(v___x_849_);
goto v___jp_823_;
}
else
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_nat_dec_eq(v_idx_853_, v___x_858_);
lean_dec(v_idx_853_);
if (v___x_859_ == 0)
{
lean_dec_ref(v_struct_854_);
lean_del_object(v___x_849_);
goto v___jp_823_;
}
else
{
if (lean_obj_tag(v_struct_854_) == 5)
{
lean_object* v_fn_860_; 
v_fn_860_ = lean_ctor_get(v_struct_854_, 0);
lean_inc_ref(v_fn_860_);
lean_dec_ref_known(v_struct_854_, 2);
if (lean_obj_tag(v_fn_860_) == 4)
{
lean_object* v_declName_861_; 
v_declName_861_ = lean_ctor_get(v_fn_860_, 0);
lean_inc(v_declName_861_);
if (lean_obj_tag(v_declName_861_) == 1)
{
lean_object* v_pre_862_; 
v_pre_862_ = lean_ctor_get(v_declName_861_, 0);
lean_inc(v_pre_862_);
if (lean_obj_tag(v_pre_862_) == 1)
{
lean_object* v_pre_863_; 
v_pre_863_ = lean_ctor_get(v_pre_862_, 0);
if (lean_obj_tag(v_pre_863_) == 0)
{
lean_object* v_us_864_; lean_object* v_str_865_; lean_object* v_str_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_us_864_ = lean_ctor_get(v_fn_860_, 1);
lean_inc(v_us_864_);
lean_dec_ref_known(v_fn_860_, 2);
v_str_865_ = lean_ctor_get(v_declName_861_, 1);
lean_inc_ref(v_str_865_);
lean_dec_ref_known(v_declName_861_, 2);
v_str_866_ = lean_ctor_get(v_pre_862_, 1);
lean_inc_ref(v_str_866_);
lean_dec_ref_known(v_pre_862_, 2);
v___x_867_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2));
v___x_868_ = lean_string_dec_eq(v_str_866_, v___x_867_);
lean_dec_ref(v_str_866_);
if (v___x_868_ == 0)
{
lean_dec_ref(v_str_865_);
lean_dec(v_us_864_);
lean_del_object(v___x_849_);
goto v___jp_823_;
}
else
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3));
v___x_870_ = lean_string_dec_eq(v_str_865_, v___x_869_);
lean_dec_ref(v_str_865_);
if (v___x_870_ == 0)
{
lean_dec(v_us_864_);
lean_del_object(v___x_849_);
goto v___jp_823_;
}
else
{
if (lean_obj_tag(v_us_864_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_del_object(v___x_818_);
v___x_871_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_872_ = l_Lean_mkConst(v___x_871_, v_us_864_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_872_);
v___x_874_ = v___x_849_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
else
{
lean_dec(v_us_864_);
lean_del_object(v___x_849_);
goto v___jp_823_;
}
}
}
}
else
{
lean_dec_ref_known(v_pre_862_, 2);
lean_dec_ref_known(v_declName_861_, 2);
lean_dec_ref_known(v_fn_860_, 2);
lean_del_object(v___x_849_);
goto v___jp_823_;
}
}
else
{
lean_dec(v_pre_862_);
lean_dec_ref_known(v_declName_861_, 2);
lean_dec_ref_known(v_fn_860_, 2);
lean_del_object(v___x_849_);
goto v___jp_823_;
}
}
else
{
lean_dec(v_declName_861_);
lean_dec_ref_known(v_fn_860_, 2);
lean_del_object(v___x_849_);
goto v___jp_823_;
}
}
else
{
lean_dec_ref(v_fn_860_);
lean_del_object(v___x_849_);
goto v___jp_823_;
}
}
else
{
lean_dec_ref(v_struct_854_);
lean_del_object(v___x_849_);
goto v___jp_823_;
}
}
}
}
else
{
lean_dec_ref_known(v_typeName_851_, 2);
lean_del_object(v___x_849_);
lean_dec_ref_known(v_a_822_, 3);
goto v___jp_823_;
}
}
else
{
lean_dec(v_typeName_851_);
lean_del_object(v___x_849_);
lean_dec_ref_known(v_a_822_, 3);
goto v___jp_823_;
}
}
}
default: 
{
lean_dec(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
goto v___jp_823_;
}
}
v___jp_823_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_824_);
v___x_826_ = v___x_818_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_del_object(v___x_818_);
return v___x_821_;
}
}
else
{
lean_object* v___x_878_; lean_object* v___x_880_; 
lean_dec_ref(v_type_809_);
v___x_878_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_878_);
v___x_880_ = v___x_818_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v_type_809_);
v_a_883_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_815_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_815_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(lean_object* v_as_891_, size_t v_sz_892_, size_t v_i_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_a_901_; uint8_t v___x_905_; 
v___x_905_ = lean_usize_dec_lt(v_i_893_, v_sz_892_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v_b_894_);
return v___x_906_;
}
else
{
lean_object* v_a_907_; lean_object* v___y_909_; lean_object* v___x_938_; 
v_a_907_ = lean_array_uget_borrowed(v_as_891_, v_i_893_);
lean_inc(v_a_907_);
v___x_938_ = l_Lean_Meta_isProp(v_a_907_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; uint8_t v___x_940_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
v___x_940_ = lean_unbox(v_a_939_);
lean_dec(v_a_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
lean_dec_ref_known(v___x_938_, 1);
lean_inc(v_a_907_);
v___x_941_ = l_Lean_Compiler_LCNF_isPropFormer(v_a_907_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
v___y_909_ = v___x_941_;
goto v___jp_908_;
}
else
{
v___y_909_ = v___x_938_;
goto v___jp_908_;
}
}
else
{
v___y_909_ = v___x_938_;
goto v___jp_908_;
}
v___jp_908_:
{
if (lean_obj_tag(v___y_909_) == 0)
{
lean_object* v_a_910_; uint8_t v___x_911_; 
v_a_910_ = lean_ctor_get(v___y_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___y_909_, 1);
v___x_911_ = lean_unbox(v_a_910_);
lean_dec(v_a_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
lean_inc(v_a_907_);
v___x_912_ = l_Lean_Meta_isTypeFormer(v_a_907_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; uint8_t v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = lean_unbox(v_a_913_);
lean_dec(v_a_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_916_ = l_Lean_Expr_app___override(v_b_894_, v___x_915_);
v_a_901_ = v___x_916_;
goto v___jp_900_;
}
else
{
lean_object* v___x_917_; 
lean_inc(v_a_907_);
v___x_917_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_a_907_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v___x_919_ = l_Lean_Expr_app___override(v_b_894_, v_a_918_);
v_a_901_ = v___x_919_;
goto v___jp_900_;
}
else
{
lean_dec_ref(v_b_894_);
return v___x_917_;
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec_ref(v_b_894_);
v_a_920_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_912_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_912_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_929_ = l_Lean_Expr_app___override(v_b_894_, v___x_928_);
v_a_901_ = v___x_929_;
goto v___jp_900_;
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec_ref(v_b_894_);
v_a_930_ = lean_ctor_get(v___y_909_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___y_909_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___y_909_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___y_909_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
v___jp_900_:
{
size_t v___x_902_; size_t v___x_903_; 
v___x_902_ = ((size_t)1ULL);
v___x_903_ = lean_usize_add(v_i_893_, v___x_902_);
v_i_893_ = v___x_903_;
v_b_894_ = v_a_901_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(lean_object* v_f_945_, lean_object* v_args_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_fNew_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; 
switch(lean_obj_tag(v_f_945_))
{
case 4:
{
lean_object* v_declName_961_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___x_985_; lean_object* v_env_986_; uint8_t v_isExporting_987_; 
v_declName_961_ = lean_ctor_get(v_f_945_, 0);
v___x_985_ = lean_st_ref_get(v_a_950_);
v_env_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc_ref(v_env_986_);
lean_dec(v___x_985_);
v_isExporting_987_ = lean_ctor_get_uint8(v_env_986_, sizeof(void*)*8);
lean_dec_ref(v_env_986_);
if (v_isExporting_987_ == 0)
{
v___y_963_ = v_a_947_;
v___y_964_ = v_a_948_;
v___y_965_ = v_a_949_;
v___y_966_ = v_a_950_;
goto v___jp_962_;
}
else
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_isPrivateName(v_declName_961_);
if (v___x_988_ == 0)
{
v___y_963_ = v_a_947_;
v___y_964_ = v_a_948_;
v___y_965_ = v_a_949_;
v___y_966_ = v_a_950_;
goto v___jp_962_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1);
v___x_990_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_989_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_dec_ref_known(v___x_990_, 1);
v___y_963_ = v_a_947_;
v___y_964_ = v_a_948_;
v___y_965_ = v_a_949_;
v___y_966_ = v_a_950_;
goto v___jp_962_;
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref_known(v_f_945_, 2);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
v___jp_962_:
{
lean_object* v___x_967_; 
lean_inc(v_declName_961_);
v___x_967_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_declName_961_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_976_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_976_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
if (lean_obj_tag(v_a_968_) == 5)
{
lean_dec_ref_known(v_a_968_, 1);
lean_del_object(v___x_970_);
v_fNew_953_ = v_f_945_;
v___y_954_ = v___y_963_;
v___y_955_ = v___y_964_;
v___y_956_ = v___y_965_;
v___y_957_ = v___y_966_;
goto v___jp_952_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_974_; 
lean_dec(v_a_968_);
lean_dec_ref_known(v_f_945_, 2);
v___x_972_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref_known(v_f_945_, 2);
v_a_977_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_967_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_967_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
case 1:
{
v_fNew_953_ = v_f_945_;
v___y_954_ = v_a_947_;
v___y_955_ = v_a_948_;
v___y_956_ = v_a_949_;
v___y_957_ = v_a_950_;
goto v___jp_952_;
}
default: 
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec_ref(v_f_945_);
v___x_999_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
v___jp_952_:
{
size_t v_sz_958_; size_t v___x_959_; lean_object* v___x_960_; 
v_sz_958_ = lean_array_size(v_args_946_);
v___x_959_ = ((size_t)0ULL);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_args_946_, v_sz_958_, v___x_959_, v_fNew_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
if (lean_obj_tag(v_x_1001_) == 5)
{
lean_object* v_fn_1009_; lean_object* v_arg_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_fn_1009_ = lean_ctor_get(v_x_1001_, 0);
lean_inc_ref(v_fn_1009_);
v_arg_1010_ = lean_ctor_get(v_x_1001_, 1);
lean_inc_ref(v_arg_1010_);
lean_dec_ref_known(v_x_1001_, 2);
v___x_1011_ = lean_array_set(v_x_1002_, v_x_1003_, v_arg_1010_);
v___x_1012_ = lean_unsigned_to_nat(1u);
v___x_1013_ = lean_nat_sub(v_x_1003_, v___x_1012_);
lean_dec(v_x_1003_);
v_x_1001_ = v_fn_1009_;
v_x_1002_ = v___x_1011_;
v_x_1003_ = v___x_1013_;
goto _start;
}
else
{
lean_object* v___x_1015_; 
lean_dec(v_x_1003_);
v___x_1015_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_x_1001_, v_x_1002_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec_ref(v_x_1002_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0___boxed(lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_x_1016_, v_x_1017_, v_x_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___boxed(lean_object* v_e_1025_, lean_object* v_xs_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_e_1025_, v_xs_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___boxed(lean_object* v_f_1033_, lean_object* v_args_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_f_1033_, v_args_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec_ref(v_args_1034_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3___boxed(lean_object* v_as_1041_, lean_object* v_sz_1042_, lean_object* v_i_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
size_t v_sz_boxed_1050_; size_t v_i_boxed_1051_; lean_object* v_res_1052_; 
v_sz_boxed_1050_ = lean_unbox_usize(v_sz_1042_);
lean_dec(v_sz_1042_);
v_i_boxed_1051_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_res_1052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_as_1041_, v_sz_boxed_1050_, v_i_boxed_1051_, v_b_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec_ref(v_as_1041_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed(lean_object* v_type_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(lean_object* v_00_u03b1_1060_, lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___boxed(lean_object* v_00_u03b1_1068_, lean_object* v_msg_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(v_00_u03b1_1068_, v_msg_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(lean_object* v_00_u03b1_1076_, lean_object* v_constName_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___boxed(lean_object* v_00_u03b1_1084_, lean_object* v_constName_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(v_00_u03b1_1084_, v_constName_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(lean_object* v_00_u03b1_1092_, lean_object* v_ref_1093_, lean_object* v_constName_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_1093_, v_constName_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1101_, lean_object* v_ref_1102_, lean_object* v_constName_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(v_00_u03b1_1101_, v_ref_1102_, v_constName_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v_ref_1102_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(lean_object* v_00_u03b1_1110_, lean_object* v_ref_1111_, lean_object* v_msg_1112_, lean_object* v_declHint_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_1111_, v_msg_1112_, v_declHint_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_ref_1121_, lean_object* v_msg_1122_, lean_object* v_declHint_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(v_00_u03b1_1120_, v_ref_1121_, v_msg_1122_, v_declHint_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v_ref_1121_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(lean_object* v_msg_1130_, lean_object* v_declHint_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1130_, v_declHint_1131_, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_1138_, lean_object* v_declHint_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(v_msg_1138_, v_declHint_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(lean_object* v_00_u03b1_1146_, lean_object* v_ref_1147_, lean_object* v_msg_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1147_, v_msg_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_ref_1156_, lean_object* v_msg_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(v_00_u03b1_1155_, v_ref_1156_, v_msg_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v_ref_1156_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(lean_object* v___y_1164_, uint8_t v_isExporting_1165_, lean_object* v___x_1166_, lean_object* v___y_1167_, lean_object* v___x_1168_, lean_object* v_a_x3f_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v_env_1172_; lean_object* v_nextMacroScope_1173_; lean_object* v_ngen_1174_; lean_object* v_auxDeclNGen_1175_; lean_object* v_traceState_1176_; lean_object* v_messages_1177_; lean_object* v_infoState_1178_; lean_object* v_snapshotTasks_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1204_; 
v___x_1171_ = lean_st_ref_take(v___y_1164_);
v_env_1172_ = lean_ctor_get(v___x_1171_, 0);
v_nextMacroScope_1173_ = lean_ctor_get(v___x_1171_, 1);
v_ngen_1174_ = lean_ctor_get(v___x_1171_, 2);
v_auxDeclNGen_1175_ = lean_ctor_get(v___x_1171_, 3);
v_traceState_1176_ = lean_ctor_get(v___x_1171_, 4);
v_messages_1177_ = lean_ctor_get(v___x_1171_, 6);
v_infoState_1178_ = lean_ctor_get(v___x_1171_, 7);
v_snapshotTasks_1179_ = lean_ctor_get(v___x_1171_, 8);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v___x_1171_, 5);
lean_dec(v_unused_1205_);
v___x_1181_ = v___x_1171_;
v_isShared_1182_ = v_isSharedCheck_1204_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_snapshotTasks_1179_);
lean_inc(v_infoState_1178_);
lean_inc(v_messages_1177_);
lean_inc(v_traceState_1176_);
lean_inc(v_auxDeclNGen_1175_);
lean_inc(v_ngen_1174_);
lean_inc(v_nextMacroScope_1173_);
lean_inc(v_env_1172_);
lean_dec(v___x_1171_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1204_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = l_Lean_Environment_setExporting(v_env_1172_, v_isExporting_1165_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 5, v___x_1166_);
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_nextMacroScope_1173_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_ngen_1174_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_auxDeclNGen_1175_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_traceState_1176_);
lean_ctor_set(v_reuseFailAlloc_1203_, 5, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1203_, 6, v_messages_1177_);
lean_ctor_set(v_reuseFailAlloc_1203_, 7, v_infoState_1178_);
lean_ctor_set(v_reuseFailAlloc_1203_, 8, v_snapshotTasks_1179_);
v___x_1185_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v_mctx_1188_; lean_object* v_zetaDeltaFVarIds_1189_; lean_object* v_postponed_1190_; lean_object* v_diag_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1201_; 
v___x_1186_ = lean_st_ref_set(v___y_1164_, v___x_1185_);
v___x_1187_ = lean_st_ref_take(v___y_1167_);
v_mctx_1188_ = lean_ctor_get(v___x_1187_, 0);
v_zetaDeltaFVarIds_1189_ = lean_ctor_get(v___x_1187_, 2);
v_postponed_1190_ = lean_ctor_get(v___x_1187_, 3);
v_diag_1191_ = lean_ctor_get(v___x_1187_, 4);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1187_, 1);
lean_dec(v_unused_1202_);
v___x_1193_ = v___x_1187_;
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_diag_1191_);
lean_inc(v_postponed_1190_);
lean_inc(v_zetaDeltaFVarIds_1189_);
lean_inc(v_mctx_1188_);
lean_dec(v___x_1187_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1168_);
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_mctx_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_zetaDeltaFVarIds_1189_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_postponed_1190_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_diag_1191_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_st_ref_set(v___y_1167_, v___x_1196_);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0___boxed(lean_object* v___y_1206_, lean_object* v_isExporting_1207_, lean_object* v___x_1208_, lean_object* v___y_1209_, lean_object* v___x_1210_, lean_object* v_a_x3f_1211_, lean_object* v___y_1212_){
_start:
{
uint8_t v_isExporting_boxed_1213_; lean_object* v_res_1214_; 
v_isExporting_boxed_1213_ = lean_unbox(v_isExporting_1207_);
v_res_1214_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1206_, v_isExporting_boxed_1213_, v___x_1208_, v___y_1209_, v___x_1210_, v_a_x3f_1211_);
lean_dec(v_a_x3f_1211_);
lean_dec(v___y_1209_);
lean_dec(v___y_1206_);
return v_res_1214_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
v___x_1221_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
lean_ctor_set(v___x_1221_, 2, v___x_1220_);
lean_ctor_set(v___x_1221_, 3, v___x_1220_);
lean_ctor_set(v___x_1221_, 4, v___x_1220_);
lean_ctor_set(v___x_1221_, 5, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(lean_object* v_x_1222_, uint8_t v_isExporting_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; lean_object* v_env_1230_; uint8_t v_isExporting_1231_; uint8_t v___y_1298_; lean_object* v___x_1300_; uint8_t v_isModule_1301_; uint8_t v___x_1302_; 
v___x_1229_ = lean_st_ref_get(v___y_1227_);
v_env_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc_ref(v_env_1230_);
lean_dec(v___x_1229_);
v_isExporting_1231_ = lean_ctor_get_uint8(v_env_1230_, sizeof(void*)*8);
v___x_1300_ = l_Lean_Environment_header(v_env_1230_);
lean_dec_ref(v_env_1230_);
v_isModule_1301_ = lean_ctor_get_uint8(v___x_1300_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1300_);
v___x_1302_ = lean_bool_not(v_isModule_1301_);
if (v___x_1302_ == 0)
{
if (v_isExporting_1231_ == 0)
{
if (v_isExporting_1223_ == 0)
{
lean_object* v___x_1303_; 
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
v___x_1303_ = lean_apply_5(v_x_1222_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
return v___x_1303_;
}
else
{
goto v___jp_1232_;
}
}
else
{
v___y_1298_ = v_isExporting_1223_;
goto v___jp_1297_;
}
}
else
{
v___y_1298_ = v___x_1302_;
goto v___jp_1297_;
}
v___jp_1232_:
{
lean_object* v___x_1233_; lean_object* v_env_1234_; lean_object* v_nextMacroScope_1235_; lean_object* v_ngen_1236_; lean_object* v_auxDeclNGen_1237_; lean_object* v_traceState_1238_; lean_object* v_messages_1239_; lean_object* v_infoState_1240_; lean_object* v_snapshotTasks_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1295_; 
v___x_1233_ = lean_st_ref_take(v___y_1227_);
v_env_1234_ = lean_ctor_get(v___x_1233_, 0);
v_nextMacroScope_1235_ = lean_ctor_get(v___x_1233_, 1);
v_ngen_1236_ = lean_ctor_get(v___x_1233_, 2);
v_auxDeclNGen_1237_ = lean_ctor_get(v___x_1233_, 3);
v_traceState_1238_ = lean_ctor_get(v___x_1233_, 4);
v_messages_1239_ = lean_ctor_get(v___x_1233_, 6);
v_infoState_1240_ = lean_ctor_get(v___x_1233_, 7);
v_snapshotTasks_1241_ = lean_ctor_get(v___x_1233_, 8);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v___x_1233_, 5);
lean_dec(v_unused_1296_);
v___x_1243_ = v___x_1233_;
v_isShared_1244_ = v_isSharedCheck_1295_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_snapshotTasks_1241_);
lean_inc(v_infoState_1240_);
lean_inc(v_messages_1239_);
lean_inc(v_traceState_1238_);
lean_inc(v_auxDeclNGen_1237_);
lean_inc(v_ngen_1236_);
lean_inc(v_nextMacroScope_1235_);
lean_inc(v_env_1234_);
lean_dec(v___x_1233_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1295_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1245_ = l_Lean_Environment_setExporting(v_env_1234_, v_isExporting_1223_);
v___x_1246_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 5, v___x_1246_);
lean_ctor_set(v___x_1243_, 0, v___x_1245_);
v___x_1248_ = v___x_1243_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_nextMacroScope_1235_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_ngen_1236_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_auxDeclNGen_1237_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v_traceState_1238_);
lean_ctor_set(v_reuseFailAlloc_1294_, 5, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1294_, 6, v_messages_1239_);
lean_ctor_set(v_reuseFailAlloc_1294_, 7, v_infoState_1240_);
lean_ctor_set(v_reuseFailAlloc_1294_, 8, v_snapshotTasks_1241_);
v___x_1248_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v_mctx_1251_; lean_object* v_zetaDeltaFVarIds_1252_; lean_object* v_postponed_1253_; lean_object* v_diag_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1292_; 
v___x_1249_ = lean_st_ref_set(v___y_1227_, v___x_1248_);
v___x_1250_ = lean_st_ref_take(v___y_1225_);
v_mctx_1251_ = lean_ctor_get(v___x_1250_, 0);
v_zetaDeltaFVarIds_1252_ = lean_ctor_get(v___x_1250_, 2);
v_postponed_1253_ = lean_ctor_get(v___x_1250_, 3);
v_diag_1254_ = lean_ctor_get(v___x_1250_, 4);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1250_, 1);
lean_dec(v_unused_1293_);
v___x_1256_ = v___x_1250_;
v_isShared_1257_ = v_isSharedCheck_1292_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_diag_1254_);
lean_inc(v_postponed_1253_);
lean_inc(v_zetaDeltaFVarIds_1252_);
lean_inc(v_mctx_1251_);
lean_dec(v___x_1250_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1292_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1258_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_mctx_1251_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_zetaDeltaFVarIds_1252_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_postponed_1253_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_diag_1254_);
v___x_1260_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; lean_object* v_r_1262_; 
v___x_1261_ = lean_st_ref_set(v___y_1225_, v___x_1260_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
v_r_1262_ = lean_apply_5(v_x_1222_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
if (lean_obj_tag(v_r_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1279_; 
v_a_1263_ = lean_ctor_get(v_r_1262_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_r_1262_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1265_ = v_r_1262_;
v_isShared_1266_ = v_isSharedCheck_1279_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v_r_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1279_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
lean_inc(v_a_1263_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set_tag(v___x_1265_, 1);
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
v___x_1269_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1227_, v_isExporting_1231_, v___x_1246_, v___y_1225_, v___x_1258_, v___x_1268_);
lean_dec_ref(v___x_1268_);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; 
v_unused_1277_ = lean_ctor_get(v___x_1269_, 0);
lean_dec(v_unused_1277_);
v___x_1271_ = v___x_1269_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_dec(v___x_1269_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v_a_1263_);
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1263_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1280_ = lean_ctor_get(v_r_1262_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v_r_1262_, 1);
v___x_1281_ = lean_box(0);
v___x_1282_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1227_, v_isExporting_1231_, v___x_1246_, v___y_1225_, v___x_1258_, v___x_1281_);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v___x_1282_, 0);
lean_dec(v_unused_1290_);
v___x_1284_ = v___x_1282_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_dec(v___x_1282_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 1);
lean_ctor_set(v___x_1284_, 0, v_a_1280_);
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1280_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
}
}
}
v___jp_1297_:
{
if (v___y_1298_ == 0)
{
goto v___jp_1232_;
}
else
{
lean_object* v___x_1299_; 
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
v___x_1299_ = lean_apply_5(v_x_1222_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___boxed(lean_object* v_x_1304_, lean_object* v_isExporting_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
uint8_t v_isExporting_boxed_1311_; lean_object* v_res_1312_; 
v_isExporting_boxed_1311_ = lean_unbox(v_isExporting_1305_);
v_res_1312_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1304_, v_isExporting_boxed_1311_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object* v_00_u03b1_1313_, lean_object* v_x_1314_, uint8_t v_isExporting_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1314_, v_isExporting_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___boxed(lean_object* v_00_u03b1_1322_, lean_object* v_x_1323_, lean_object* v_isExporting_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v_isExporting_boxed_1330_; lean_object* v_res_1331_; 
v_isExporting_boxed_1330_ = lean_unbox(v_isExporting_1324_);
v_res_1331_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(v_00_u03b1_1322_, v_x_1323_, v_isExporting_boxed_1330_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1331_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(lean_object* v_opts_1332_, lean_object* v_opt_1333_){
_start:
{
lean_object* v_name_1334_; lean_object* v_defValue_1335_; lean_object* v_map_1336_; lean_object* v___x_1337_; 
v_name_1334_ = lean_ctor_get(v_opt_1333_, 0);
v_defValue_1335_ = lean_ctor_get(v_opt_1333_, 1);
v_map_1336_ = lean_ctor_get(v_opts_1332_, 0);
v___x_1337_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1336_, v_name_1334_);
if (lean_obj_tag(v___x_1337_) == 0)
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_unbox(v_defValue_1335_);
return v___x_1338_;
}
else
{
lean_object* v_val_1339_; 
v_val_1339_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_val_1339_);
lean_dec_ref_known(v___x_1337_, 1);
if (lean_obj_tag(v_val_1339_) == 1)
{
uint8_t v_v_1340_; 
v_v_1340_ = lean_ctor_get_uint8(v_val_1339_, 0);
lean_dec_ref_known(v_val_1339_, 0);
return v_v_1340_;
}
else
{
uint8_t v___x_1341_; 
lean_dec(v_val_1339_);
v___x_1341_ = lean_unbox(v_defValue_1335_);
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5___boxed(lean_object* v_opts_1342_, lean_object* v_opt_1343_){
_start:
{
uint8_t v_res_1344_; lean_object* v_r_1345_; 
v_res_1344_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v_opts_1342_, v_opt_1343_);
lean_dec_ref(v_opt_1343_);
lean_dec_ref(v_opts_1342_);
v_r_1345_ = lean_box(v_res_1344_);
return v_r_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(lean_object* v_opts_1346_, lean_object* v_opt_1347_){
_start:
{
lean_object* v_name_1348_; lean_object* v_defValue_1349_; lean_object* v_map_1350_; lean_object* v___x_1351_; 
v_name_1348_ = lean_ctor_get(v_opt_1347_, 0);
v_defValue_1349_ = lean_ctor_get(v_opt_1347_, 1);
v_map_1350_ = lean_ctor_get(v_opts_1346_, 0);
v___x_1351_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1350_, v_name_1348_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_inc(v_defValue_1349_);
return v_defValue_1349_;
}
else
{
lean_object* v_val_1352_; 
v_val_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_val_1352_);
lean_dec_ref_known(v___x_1351_, 1);
if (lean_obj_tag(v_val_1352_) == 3)
{
lean_object* v_v_1353_; 
v_v_1353_ = lean_ctor_get(v_val_1352_, 0);
lean_inc(v_v_1353_);
lean_dec_ref_known(v_val_1352_, 1);
return v_v_1353_;
}
else
{
lean_dec(v_val_1352_);
lean_inc(v_defValue_1349_);
return v_defValue_1349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6___boxed(lean_object* v_opts_1354_, lean_object* v_opt_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(v_opts_1354_, v_opt_1355_);
lean_dec_ref(v_opt_1355_);
lean_dec_ref(v_opts_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object* v_a_1357_, lean_object* v_diag_1358_, lean_object* v_a_x3f_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v_mctx_1362_; lean_object* v_cache_1363_; lean_object* v_zetaDeltaFVarIds_1364_; lean_object* v_postponed_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1375_; 
v___x_1361_ = lean_st_ref_take(v_a_1357_);
v_mctx_1362_ = lean_ctor_get(v___x_1361_, 0);
v_cache_1363_ = lean_ctor_get(v___x_1361_, 1);
v_zetaDeltaFVarIds_1364_ = lean_ctor_get(v___x_1361_, 2);
v_postponed_1365_ = lean_ctor_get(v___x_1361_, 3);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v___x_1361_, 4);
lean_dec(v_unused_1376_);
v___x_1367_ = v___x_1361_;
v_isShared_1368_ = v_isSharedCheck_1375_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_postponed_1365_);
lean_inc(v_zetaDeltaFVarIds_1364_);
lean_inc(v_cache_1363_);
lean_inc(v_mctx_1362_);
lean_dec(v___x_1361_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1375_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 4, v_diag_1358_);
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_mctx_1362_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_cache_1363_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_zetaDeltaFVarIds_1364_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_postponed_1365_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_diag_1358_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = lean_st_ref_set(v_a_1357_, v___x_1370_);
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object* v_a_1377_, lean_object* v_diag_1378_, lean_object* v_a_x3f_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1377_, v_diag_1378_, v_a_x3f_1379_);
lean_dec(v_a_x3f_1379_);
lean_dec(v_a_1377_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0(lean_object* v_ps_1382_, lean_object* v_k_1383_, lean_object* v_v_1384_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_k_1383_);
lean_ctor_set(v___x_1385_, 1, v_v_1384_);
v___x_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v_ps_1382_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(lean_object* v_f_1387_, lean_object* v_keys_1388_, lean_object* v_vals_1389_, lean_object* v_i_1390_, lean_object* v_acc_1391_){
_start:
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = lean_array_get_size(v_keys_1388_);
v___x_1393_ = lean_nat_dec_lt(v_i_1390_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_dec(v_i_1390_);
lean_dec(v_f_1387_);
return v_acc_1391_;
}
else
{
lean_object* v_k_1394_; lean_object* v_v_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_k_1394_ = lean_array_fget_borrowed(v_keys_1388_, v_i_1390_);
v_v_1395_ = lean_array_fget_borrowed(v_vals_1389_, v_i_1390_);
lean_inc(v_f_1387_);
lean_inc(v_v_1395_);
lean_inc(v_k_1394_);
v___x_1396_ = lean_apply_3(v_f_1387_, v_acc_1391_, v_k_1394_, v_v_1395_);
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = lean_nat_add(v_i_1390_, v___x_1397_);
lean_dec(v_i_1390_);
v_i_1390_ = v___x_1398_;
v_acc_1391_ = v___x_1396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_f_1400_, lean_object* v_keys_1401_, lean_object* v_vals_1402_, lean_object* v_i_1403_, lean_object* v_acc_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1400_, v_keys_1401_, v_vals_1402_, v_i_1403_, v_acc_1404_);
lean_dec_ref(v_vals_1402_);
lean_dec_ref(v_keys_1401_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(lean_object* v_f_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
lean_object* v_es_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_es_1409_ = lean_ctor_get(v_x_1407_, 0);
v___x_1410_ = lean_unsigned_to_nat(0u);
v___x_1411_ = lean_array_get_size(v_es_1409_);
v___x_1412_ = lean_nat_dec_lt(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_dec(v_f_1406_);
return v_x_1408_;
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_nat_dec_le(v___x_1411_, v___x_1411_);
if (v___x_1413_ == 0)
{
if (v___x_1412_ == 0)
{
lean_dec(v_f_1406_);
return v_x_1408_;
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1411_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1406_, v_es_1409_, v___x_1414_, v___x_1415_, v_x_1408_);
return v___x_1416_;
}
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1411_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1406_, v_es_1409_, v___x_1417_, v___x_1418_, v_x_1408_);
return v___x_1419_;
}
}
}
else
{
lean_object* v_ks_1420_; lean_object* v_vs_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_ks_1420_ = lean_ctor_get(v_x_1407_, 0);
v_vs_1421_ = lean_ctor_get(v_x_1407_, 1);
v___x_1422_ = lean_unsigned_to_nat(0u);
v___x_1423_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1406_, v_ks_1420_, v_vs_1421_, v___x_1422_, v_x_1408_);
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(lean_object* v_f_1424_, lean_object* v_as_1425_, size_t v_i_1426_, size_t v_stop_1427_, lean_object* v_b_1428_){
_start:
{
lean_object* v___y_1430_; uint8_t v___x_1434_; 
v___x_1434_ = lean_usize_dec_eq(v_i_1426_, v_stop_1427_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_array_uget_borrowed(v_as_1425_, v_i_1426_);
switch(lean_obj_tag(v___x_1435_))
{
case 0:
{
lean_object* v_key_1436_; lean_object* v_val_1437_; lean_object* v___x_1438_; 
v_key_1436_ = lean_ctor_get(v___x_1435_, 0);
v_val_1437_ = lean_ctor_get(v___x_1435_, 1);
lean_inc(v_f_1424_);
lean_inc(v_val_1437_);
lean_inc(v_key_1436_);
v___x_1438_ = lean_apply_3(v_f_1424_, v_b_1428_, v_key_1436_, v_val_1437_);
v___y_1430_ = v___x_1438_;
goto v___jp_1429_;
}
case 1:
{
lean_object* v_node_1439_; lean_object* v___x_1440_; 
v_node_1439_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_f_1424_);
v___x_1440_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1424_, v_node_1439_, v_b_1428_);
v___y_1430_ = v___x_1440_;
goto v___jp_1429_;
}
default: 
{
v___y_1430_ = v_b_1428_;
goto v___jp_1429_;
}
}
}
else
{
lean_dec(v_f_1424_);
return v_b_1428_;
}
v___jp_1429_:
{
size_t v___x_1431_; size_t v___x_1432_; 
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_add(v_i_1426_, v___x_1431_);
v_i_1426_ = v___x_1432_;
v_b_1428_ = v___y_1430_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg___boxed(lean_object* v_f_1441_, lean_object* v_as_1442_, lean_object* v_i_1443_, lean_object* v_stop_1444_, lean_object* v_b_1445_){
_start:
{
size_t v_i_boxed_1446_; size_t v_stop_boxed_1447_; lean_object* v_res_1448_; 
v_i_boxed_1446_ = lean_unbox_usize(v_i_1443_);
lean_dec(v_i_1443_);
v_stop_boxed_1447_ = lean_unbox_usize(v_stop_1444_);
lean_dec(v_stop_1444_);
v_res_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1441_, v_as_1442_, v_i_boxed_1446_, v_stop_boxed_1447_, v_b_1445_);
lean_dec_ref(v_as_1442_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_f_1449_, lean_object* v_x_1450_, lean_object* v_x_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1449_, v_x_1450_, v_x_1451_);
lean_dec_ref(v_x_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0(lean_object* v_f_1453_, lean_object* v_x1_1454_, lean_object* v_x2_1455_, lean_object* v_x3_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_apply_3(v_f_1453_, v_x1_1454_, v_x2_1455_, v_x3_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(lean_object* v_map_1458_, lean_object* v_f_1459_, lean_object* v_init_1460_){
_start:
{
lean_object* v___f_1461_; lean_object* v___x_1462_; 
v___f_1461_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1461_, 0, v_f_1459_);
v___x_1462_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v___f_1461_, v_map_1458_, v_init_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___boxed(lean_object* v_map_1463_, lean_object* v_f_1464_, lean_object* v_init_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_1463_, v_f_1464_, v_init_1465_);
lean_dec_ref(v_map_1463_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(lean_object* v_m_1468_){
_start:
{
lean_object* v___f_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___f_1469_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0));
v___x_1470_ = lean_box(0);
v___x_1471_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_m_1468_, v___f_1469_, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___boxed(lean_object* v_m_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1472_);
lean_dec_ref(v_m_1472_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(lean_object* v_o_1477_, lean_object* v_k_1478_, uint8_t v_v_1479_){
_start:
{
lean_object* v_map_1480_; uint8_t v_hasTrace_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1495_; 
v_map_1480_ = lean_ctor_get(v_o_1477_, 0);
v_hasTrace_1481_ = lean_ctor_get_uint8(v_o_1477_, sizeof(void*)*1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_o_1477_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1483_ = v_o_1477_;
v_isShared_1484_ = v_isSharedCheck_1495_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_map_1480_);
lean_dec(v_o_1477_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1495_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1485_, 0, v_v_1479_);
lean_inc(v_k_1478_);
v___x_1486_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1478_, v___x_1485_, v_map_1480_);
if (v_hasTrace_1481_ == 0)
{
lean_object* v___x_1487_; uint8_t v___x_1488_; lean_object* v___x_1490_; 
v___x_1487_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1));
v___x_1488_ = l_Lean_Name_isPrefixOf(v___x_1487_, v_k_1478_);
lean_dec(v_k_1478_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1486_);
v___x_1490_ = v___x_1483_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1486_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*1, v___x_1488_);
return v___x_1490_;
}
}
else
{
lean_object* v___x_1493_; 
lean_dec(v_k_1478_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1486_);
v___x_1493_ = v___x_1483_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*1, v_hasTrace_1481_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___boxed(lean_object* v_o_1496_, lean_object* v_k_1497_, lean_object* v_v_1498_){
_start:
{
uint8_t v_v_boxed_1499_; lean_object* v_res_1500_; 
v_v_boxed_1499_ = lean_unbox(v_v_1498_);
v_res_1500_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(v_o_1496_, v_k_1497_, v_v_boxed_1499_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(lean_object* v_opts_1501_, lean_object* v_opt_1502_, uint8_t v_val_1503_){
_start:
{
lean_object* v_name_1504_; lean_object* v___x_1505_; 
v_name_1504_ = lean_ctor_get(v_opt_1502_, 0);
lean_inc(v_name_1504_);
lean_dec_ref(v_opt_1502_);
v___x_1505_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(v_opts_1501_, v_name_1504_, v_val_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4___boxed(lean_object* v_opts_1506_, lean_object* v_opt_1507_, lean_object* v_val_1508_){
_start:
{
uint8_t v_val_boxed_1509_; lean_object* v_res_1510_; 
v_val_boxed_1509_ = lean_unbox(v_val_1508_);
v_res_1510_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v_opts_1506_, v_opt_1507_, v_val_boxed_1509_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(lean_object* v_keys_1511_, lean_object* v_vals_1512_, lean_object* v_i_1513_, lean_object* v_k_1514_){
_start:
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = lean_array_get_size(v_keys_1511_);
v___x_1516_ = lean_nat_dec_lt(v_i_1513_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_dec(v_i_1513_);
v___x_1517_ = lean_box(0);
return v___x_1517_;
}
else
{
lean_object* v_k_x27_1518_; uint8_t v___x_1519_; 
v_k_x27_1518_ = lean_array_fget_borrowed(v_keys_1511_, v_i_1513_);
v___x_1519_ = lean_name_eq(v_k_1514_, v_k_x27_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_nat_add(v_i_1513_, v___x_1520_);
lean_dec(v_i_1513_);
v_i_1513_ = v___x_1521_;
goto _start;
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_array_fget_borrowed(v_vals_1512_, v_i_1513_);
lean_dec(v_i_1513_);
lean_inc(v___x_1523_);
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_keys_1525_, lean_object* v_vals_1526_, lean_object* v_i_1527_, lean_object* v_k_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_keys_1525_, v_vals_1526_, v_i_1527_, v_k_1528_);
lean_dec(v_k_1528_);
lean_dec_ref(v_vals_1526_);
lean_dec_ref(v_keys_1525_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(lean_object* v_x_1530_, size_t v_x_1531_, lean_object* v_x_1532_){
_start:
{
if (lean_obj_tag(v_x_1530_) == 0)
{
lean_object* v_es_1533_; lean_object* v___x_1534_; size_t v___x_1535_; size_t v___x_1536_; lean_object* v_j_1537_; lean_object* v___x_1538_; 
v_es_1533_ = lean_ctor_get(v_x_1530_, 0);
v___x_1534_ = lean_box(2);
v___x_1535_ = ((size_t)31ULL);
v___x_1536_ = lean_usize_land(v_x_1531_, v___x_1535_);
v_j_1537_ = lean_usize_to_nat(v___x_1536_);
v___x_1538_ = lean_array_get_borrowed(v___x_1534_, v_es_1533_, v_j_1537_);
lean_dec(v_j_1537_);
switch(lean_obj_tag(v___x_1538_))
{
case 0:
{
lean_object* v_key_1539_; lean_object* v_val_1540_; uint8_t v___x_1541_; 
v_key_1539_ = lean_ctor_get(v___x_1538_, 0);
v_val_1540_ = lean_ctor_get(v___x_1538_, 1);
v___x_1541_ = lean_name_eq(v_x_1532_, v_key_1539_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_box(0);
return v___x_1542_;
}
else
{
lean_object* v___x_1543_; 
lean_inc(v_val_1540_);
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_val_1540_);
return v___x_1543_;
}
}
case 1:
{
lean_object* v_node_1544_; size_t v___x_1545_; size_t v___x_1546_; 
v_node_1544_ = lean_ctor_get(v___x_1538_, 0);
v___x_1545_ = ((size_t)5ULL);
v___x_1546_ = lean_usize_shift_right(v_x_1531_, v___x_1545_);
v_x_1530_ = v_node_1544_;
v_x_1531_ = v___x_1546_;
goto _start;
}
default: 
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_box(0);
return v___x_1548_;
}
}
}
else
{
lean_object* v_ks_1549_; lean_object* v_vs_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_ks_1549_ = lean_ctor_get(v_x_1530_, 0);
v_vs_1550_ = lean_ctor_get(v_x_1530_, 1);
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_ks_1549_, v_vs_1550_, v___x_1551_, v_x_1532_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___boxed(lean_object* v_x_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_){
_start:
{
size_t v_x_18228__boxed_1556_; lean_object* v_res_1557_; 
v_x_18228__boxed_1556_ = lean_unbox_usize(v_x_1554_);
lean_dec(v_x_1554_);
v_res_1557_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1553_, v_x_18228__boxed_1556_, v_x_1555_);
lean_dec(v_x_1555_);
lean_dec_ref(v_x_1553_);
return v_res_1557_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1558_; uint64_t v___x_1559_; 
v___x_1558_ = lean_unsigned_to_nat(1723u);
v___x_1559_ = lean_uint64_of_nat(v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(lean_object* v_x_1560_, lean_object* v_x_1561_){
_start:
{
uint64_t v___y_1563_; 
if (lean_obj_tag(v_x_1561_) == 0)
{
uint64_t v___x_1566_; 
v___x_1566_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0);
v___y_1563_ = v___x_1566_;
goto v___jp_1562_;
}
else
{
uint64_t v_hash_1567_; 
v_hash_1567_ = lean_ctor_get_uint64(v_x_1561_, sizeof(void*)*2);
v___y_1563_ = v_hash_1567_;
goto v___jp_1562_;
}
v___jp_1562_:
{
size_t v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_uint64_to_usize(v___y_1563_);
v___x_1565_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1560_, v___x_1564_, v_x_1561_);
return v___x_1565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___boxed(lean_object* v_x_1568_, lean_object* v_x_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1568_, v_x_1569_);
lean_dec(v_x_1569_);
lean_dec_ref(v_x_1568_);
return v_res_1570_;
}
}
static lean_object* _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0));
v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(lean_object* v___x_1574_, lean_object* v___x_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
if (lean_obj_tag(v_a_1576_) == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref(v___x_1575_);
v___x_1578_ = lean_array_to_list(v_a_1577_);
return v___x_1578_;
}
else
{
lean_object* v_head_1579_; lean_object* v_tail_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1620_; 
v_head_1579_ = lean_ctor_get(v_a_1576_, 0);
v_tail_1580_ = lean_ctor_get(v_a_1576_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_a_1576_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1582_ = v_a_1576_;
v_isShared_1583_ = v_isSharedCheck_1620_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_tail_1580_);
lean_inc(v_head_1579_);
lean_dec(v_a_1576_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1620_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1619_; 
v_fst_1584_ = lean_ctor_get(v_head_1579_, 0);
v_snd_1585_ = lean_ctor_get(v_head_1579_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_head_1579_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1587_ = v_head_1579_;
v_isShared_1588_ = v_isSharedCheck_1619_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_snd_1585_);
lean_inc(v_fst_1584_);
lean_dec(v_head_1579_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1619_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___y_1590_; lean_object* v_unfoldAxiomCounter_1605_; lean_object* v___x_1606_; lean_object* v___y_1608_; lean_object* v___x_1617_; 
v_unfoldAxiomCounter_1605_ = lean_ctor_get(v___x_1574_, 1);
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1617_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_unfoldAxiomCounter_1605_, v_fst_1584_);
if (lean_obj_tag(v___x_1617_) == 0)
{
v___y_1608_ = v___x_1606_;
goto v___jp_1607_;
}
else
{
lean_object* v_val_1618_; 
v_val_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_val_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___y_1608_ = v_val_1618_;
goto v___jp_1607_;
}
v___jp_1589_:
{
uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1591_ = 0;
v___x_1592_ = l_Lean_MessageData_ofConstName(v_fst_1584_, v___x_1591_);
v___x_1593_ = lean_obj_once(&l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1, &l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1_once, _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1);
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 7);
lean_ctor_set(v___x_1587_, 1, v___x_1593_);
lean_ctor_set(v___x_1587_, 0, v___x_1592_);
v___x_1595_ = v___x_1587_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1596_ = l_Nat_reprFast(v___y_1590_);
v___x_1597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
v___x_1598_ = l_Lean_MessageData_ofFormat(v___x_1597_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 7);
lean_ctor_set(v___x_1582_, 1, v___x_1598_);
lean_ctor_set(v___x_1582_, 0, v___x_1595_);
v___x_1600_ = v___x_1582_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_array_push(v_a_1577_, v___x_1600_);
v_a_1576_ = v_tail_1580_;
v_a_1577_ = v___x_1601_;
goto _start;
}
}
}
v___jp_1607_:
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = lean_nat_sub(v_snd_1585_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec(v_snd_1585_);
v___x_1610_ = lean_nat_dec_lt(v___x_1606_, v___x_1609_);
if (v___x_1610_ == 0)
{
if (v___x_1610_ == 0)
{
lean_dec(v___x_1609_);
lean_del_object(v___x_1587_);
lean_dec(v_fst_1584_);
lean_del_object(v___x_1582_);
v_a_1576_ = v_tail_1580_;
goto _start;
}
else
{
v___y_1590_ = v___x_1609_;
goto v___jp_1589_;
}
}
else
{
lean_object* v___x_1612_; 
lean_inc(v_fst_1584_);
lean_inc_ref(v___x_1575_);
v___x_1612_ = l_Lean_getOriginalConstKind_x3f(v___x_1575_, v_fst_1584_);
if (lean_obj_tag(v___x_1612_) == 1)
{
lean_object* v_val_1613_; uint8_t v___x_1614_; 
v_val_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = lean_unbox(v_val_1613_);
lean_dec(v_val_1613_);
if (v___x_1614_ == 0)
{
v___y_1590_ = v___x_1609_;
goto v___jp_1589_;
}
else
{
lean_dec(v___x_1609_);
lean_del_object(v___x_1587_);
lean_dec(v_fst_1584_);
lean_del_object(v___x_1582_);
v_a_1576_ = v_tail_1580_;
goto _start;
}
}
else
{
lean_dec(v___x_1612_);
lean_dec(v___x_1609_);
lean_del_object(v___x_1587_);
lean_dec(v_fst_1584_);
lean_del_object(v___x_1582_);
v_a_1576_ = v_tail_1580_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___boxed(lean_object* v___x_1621_, lean_object* v___x_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v___x_1621_, v___x_1622_, v_a_1623_, v_a_1624_);
lean_dec_ref(v___x_1621_);
return v_res_1625_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__0));
v___x_1628_ = l_Lean_stringToMessageData(v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__2));
v___x_1631_ = l_Lean_stringToMessageData(v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__4));
v___x_1634_ = l_Lean_stringToMessageData(v___x_1633_);
return v___x_1634_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__6));
v___x_1637_ = l_Lean_stringToMessageData(v___x_1636_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__8));
v___x_1640_ = l_Lean_stringToMessageData(v___x_1639_);
return v___x_1640_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__11));
v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
return v___x_1645_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_box(1);
v___x_1647_ = l_Lean_MessageData_ofFormat(v___x_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__14));
v___x_1650_ = l_Lean_stringToMessageData(v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object* v_type_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_inc_ref(v_type_1651_);
v___x_1657_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed), 6, 1);
lean_closure_set(v___x_1657_, 0, v_type_1651_);
v___x_1658_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1832_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1832_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1832_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v_env_1664_; lean_object* v___x_1665_; uint8_t v_isModule_1666_; 
v___x_1663_ = lean_st_ref_get(v_a_1655_);
v_env_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc_ref(v_env_1664_);
lean_dec(v___x_1663_);
v___x_1665_ = l_Lean_Environment_header(v_env_1664_);
lean_dec_ref(v_env_1664_);
v_isModule_1666_ = lean_ctor_get_uint8(v___x_1665_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1665_);
if (v_isModule_1666_ == 0)
{
lean_object* v___x_1668_; 
lean_dec_ref(v___x_1657_);
if (v_isShared_1662_ == 0)
{
v___x_1668_ = v___x_1661_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1659_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
else
{
lean_object* v___x_1670_; 
lean_del_object(v___x_1661_);
lean_inc_ref(v___x_1657_);
v___x_1670_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1657_, v_isModule_1666_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1818_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1818_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1818_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
uint8_t v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = lean_expr_eqv(v_a_1659_, v_a_1671_);
v___x_1676_ = lean_bool_not(v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1678_; 
lean_dec(v_a_1671_);
lean_dec_ref(v___x_1657_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v_a_1659_);
v___x_1678_ = v___x_1673_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1659_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v_diag_1682_; lean_object* v_fileName_1683_; lean_object* v_fileMap_1684_; lean_object* v_options_1685_; lean_object* v_currRecDepth_1686_; lean_object* v_ref_1687_; lean_object* v_currNamespace_1688_; lean_object* v_openDecls_1689_; lean_object* v_initHeartbeats_1690_; lean_object* v_maxHeartbeats_1691_; lean_object* v_quotContext_1692_; lean_object* v_currMacroScope_1693_; lean_object* v_cancelTk_x3f_1694_; uint8_t v_suppressElabErrors_1695_; lean_object* v_inheritedTraceOptions_1696_; lean_object* v_env_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v_a_1712_; lean_object* v___y_1759_; uint8_t v___y_1760_; uint8_t v___x_1771_; lean_object* v_fileName_1773_; lean_object* v_fileMap_1774_; lean_object* v_currRecDepth_1775_; lean_object* v_ref_1776_; lean_object* v_currNamespace_1777_; lean_object* v_openDecls_1778_; lean_object* v_initHeartbeats_1779_; lean_object* v_maxHeartbeats_1780_; lean_object* v_quotContext_1781_; lean_object* v_currMacroScope_1782_; lean_object* v_cancelTk_x3f_1783_; uint8_t v_suppressElabErrors_1784_; lean_object* v_inheritedTraceOptions_1785_; lean_object* v___y_1786_; uint8_t v___y_1795_; uint8_t v___x_1817_; 
lean_del_object(v___x_1673_);
v___x_1680_ = lean_st_ref_get(v_a_1653_);
v___x_1681_ = lean_st_ref_get(v_a_1655_);
v_diag_1682_ = lean_ctor_get(v___x_1680_, 4);
lean_inc_ref(v_diag_1682_);
lean_dec(v___x_1680_);
v_fileName_1683_ = lean_ctor_get(v_a_1654_, 0);
v_fileMap_1684_ = lean_ctor_get(v_a_1654_, 1);
v_options_1685_ = lean_ctor_get(v_a_1654_, 2);
v_currRecDepth_1686_ = lean_ctor_get(v_a_1654_, 3);
v_ref_1687_ = lean_ctor_get(v_a_1654_, 5);
v_currNamespace_1688_ = lean_ctor_get(v_a_1654_, 6);
v_openDecls_1689_ = lean_ctor_get(v_a_1654_, 7);
v_initHeartbeats_1690_ = lean_ctor_get(v_a_1654_, 8);
v_maxHeartbeats_1691_ = lean_ctor_get(v_a_1654_, 9);
v_quotContext_1692_ = lean_ctor_get(v_a_1654_, 10);
v_currMacroScope_1693_ = lean_ctor_get(v_a_1654_, 11);
v_cancelTk_x3f_1694_ = lean_ctor_get(v_a_1654_, 12);
v_suppressElabErrors_1695_ = lean_ctor_get_uint8(v_a_1654_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1696_ = lean_ctor_get(v_a_1654_, 13);
v_env_1697_ = lean_ctor_get(v___x_1681_, 0);
lean_inc_ref(v_env_1697_);
lean_dec(v___x_1681_);
v___x_1698_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1685_);
v___x_1699_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v_options_1685_, v___x_1698_, v_isModule_1666_);
v___x_1700_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__1, &l_Lean_Compiler_LCNF_toLCNFType___closed__1_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1);
v___x_1701_ = l_Lean_MessageData_ofExpr(v_a_1659_);
v___x_1702_ = l_Lean_indentD(v___x_1701_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1700_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__3, &l_Lean_Compiler_LCNF_toLCNFType___closed__3_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = l_Lean_MessageData_ofExpr(v_a_1671_);
v___x_1707_ = l_Lean_indentD(v___x_1706_);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1705_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__5, &l_Lean_Compiler_LCNF_toLCNFType___closed__5_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5);
v___x_1710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1771_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v___x_1699_, v___x_1698_);
v___x_1817_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1697_);
lean_dec_ref(v_env_1697_);
if (v___x_1817_ == 0)
{
if (v___x_1771_ == 0)
{
v___y_1795_ = v___x_1676_;
goto v___jp_1794_;
}
else
{
v___y_1795_ = v___x_1817_;
goto v___jp_1794_;
}
}
else
{
v___y_1795_ = v___x_1771_;
goto v___jp_1794_;
}
v___jp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v_snd_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1734_; 
lean_inc_ref(v_a_1712_);
v___x_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1713_, 0, v_a_1712_);
v___x_1714_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1653_, v_diag_1682_, v___x_1713_);
lean_dec_ref_known(v___x_1713_, 1);
lean_dec_ref(v___x_1714_);
v_snd_1715_ = lean_ctor_get(v_a_1712_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_a_1712_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v_a_1712_, 0);
lean_dec(v_unused_1735_);
v___x_1717_ = v_a_1712_;
v_isShared_1718_ = v_isSharedCheck_1734_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_snd_1715_);
lean_dec(v_a_1712_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1734_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__7, &l_Lean_Compiler_LCNF_toLCNFType___closed__7_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7);
if (v_isShared_1718_ == 0)
{
lean_ctor_set_tag(v___x_1717_, 7);
lean_ctor_set(v___x_1717_, 0, v___x_1719_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_snd_1715_);
v___x_1721_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v___x_1722_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__9, &l_Lean_Compiler_LCNF_toLCNFType___closed__9_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_1723_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
v___jp_1736_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v_diag_1739_; lean_object* v_env_1740_; lean_object* v_unfoldAxiomCounter_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; uint8_t v___x_1746_; 
v___x_1737_ = lean_st_ref_get(v_a_1655_);
v___x_1738_ = lean_st_ref_get(v_a_1653_);
v_diag_1739_ = lean_ctor_get(v___x_1738_, 4);
lean_inc_ref(v_diag_1739_);
lean_dec(v___x_1738_);
v_env_1740_ = lean_ctor_get(v___x_1737_, 0);
lean_inc_ref(v_env_1740_);
lean_dec(v___x_1737_);
v_unfoldAxiomCounter_1741_ = lean_ctor_get(v_diag_1739_, 1);
lean_inc_ref(v_unfoldAxiomCounter_1741_);
lean_dec_ref(v_diag_1739_);
v___x_1742_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_unfoldAxiomCounter_1741_);
lean_dec_ref(v_unfoldAxiomCounter_1741_);
v___x_1743_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__10));
v___x_1744_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v_diag_1682_, v_env_1740_, v___x_1742_, v___x_1743_);
v___x_1745_ = l_List_isEmpty___redArg(v___x_1744_);
v___x_1746_ = lean_bool_not(v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v___x_1710_);
v_a_1712_ = v___x_1748_;
goto v___jp_1711_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec_ref_known(v___x_1710_, 2);
v___x_1749_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__12, &l_Lean_Compiler_LCNF_toLCNFType___closed__12_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12);
v___x_1750_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__13, &l_Lean_Compiler_LCNF_toLCNFType___closed__13_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13);
v___x_1751_ = l_Lean_MessageData_joinSep(v___x_1744_, v___x_1750_);
v___x_1752_ = l_Lean_indentD(v___x_1751_);
v___x_1753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1749_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__15, &l_Lean_Compiler_LCNF_toLCNFType___closed__15_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15);
v___x_1755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1753_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = lean_box(0);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___x_1755_);
v_a_1712_ = v___x_1757_;
goto v___jp_1711_;
}
}
v___jp_1758_:
{
if (v___y_1760_ == 0)
{
lean_dec_ref(v___y_1759_);
goto v___jp_1736_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref_known(v___x_1710_, 2);
v___x_1761_ = lean_box(0);
v___x_1762_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1653_, v_diag_1682_, v___x_1761_);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1762_, 0);
lean_dec(v_unused_1770_);
v___x_1764_ = v___x_1762_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v___x_1762_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 1);
lean_ctor_set(v___x_1764_, 0, v___y_1759_);
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___y_1759_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
v___jp_1772_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1787_ = l_Lean_maxRecDepth;
v___x_1788_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(v___x_1699_, v___x_1787_);
lean_inc_ref(v_inheritedTraceOptions_1785_);
lean_inc(v_cancelTk_x3f_1783_);
lean_inc(v_currMacroScope_1782_);
lean_inc(v_quotContext_1781_);
lean_inc(v_maxHeartbeats_1780_);
lean_inc(v_initHeartbeats_1779_);
lean_inc(v_openDecls_1778_);
lean_inc(v_currNamespace_1777_);
lean_inc(v_ref_1776_);
lean_inc(v_currRecDepth_1775_);
lean_inc_ref(v_fileMap_1774_);
lean_inc_ref(v_fileName_1773_);
v___x_1789_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1789_, 0, v_fileName_1773_);
lean_ctor_set(v___x_1789_, 1, v_fileMap_1774_);
lean_ctor_set(v___x_1789_, 2, v___x_1699_);
lean_ctor_set(v___x_1789_, 3, v_currRecDepth_1775_);
lean_ctor_set(v___x_1789_, 4, v___x_1788_);
lean_ctor_set(v___x_1789_, 5, v_ref_1776_);
lean_ctor_set(v___x_1789_, 6, v_currNamespace_1777_);
lean_ctor_set(v___x_1789_, 7, v_openDecls_1778_);
lean_ctor_set(v___x_1789_, 8, v_initHeartbeats_1779_);
lean_ctor_set(v___x_1789_, 9, v_maxHeartbeats_1780_);
lean_ctor_set(v___x_1789_, 10, v_quotContext_1781_);
lean_ctor_set(v___x_1789_, 11, v_currMacroScope_1782_);
lean_ctor_set(v___x_1789_, 12, v_cancelTk_x3f_1783_);
lean_ctor_set(v___x_1789_, 13, v_inheritedTraceOptions_1785_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*14, v___x_1771_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*14 + 1, v_suppressElabErrors_1784_);
v___x_1790_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1657_, v_isModule_1666_, v_a_1652_, v_a_1653_, v___x_1789_, v___y_1786_);
lean_dec_ref_known(v___x_1789_, 14);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_dec_ref_known(v___x_1790_, 1);
goto v___jp_1736_;
}
else
{
lean_object* v_a_1791_; uint8_t v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1792_ = l_Lean_Exception_isInterrupt(v_a_1791_);
if (v___x_1792_ == 0)
{
uint8_t v___x_1793_; 
lean_inc(v_a_1791_);
v___x_1793_ = l_Lean_Exception_isRuntime(v_a_1791_);
v___y_1759_ = v_a_1791_;
v___y_1760_ = v___x_1793_;
goto v___jp_1758_;
}
else
{
v___y_1759_ = v_a_1791_;
v___y_1760_ = v___x_1792_;
goto v___jp_1758_;
}
}
}
v___jp_1794_:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_bool_not(v___y_1795_);
if (v___x_1796_ == 0)
{
v_fileName_1773_ = v_fileName_1683_;
v_fileMap_1774_ = v_fileMap_1684_;
v_currRecDepth_1775_ = v_currRecDepth_1686_;
v_ref_1776_ = v_ref_1687_;
v_currNamespace_1777_ = v_currNamespace_1688_;
v_openDecls_1778_ = v_openDecls_1689_;
v_initHeartbeats_1779_ = v_initHeartbeats_1690_;
v_maxHeartbeats_1780_ = v_maxHeartbeats_1691_;
v_quotContext_1781_ = v_quotContext_1692_;
v_currMacroScope_1782_ = v_currMacroScope_1693_;
v_cancelTk_x3f_1783_ = v_cancelTk_x3f_1694_;
v_suppressElabErrors_1784_ = v_suppressElabErrors_1695_;
v_inheritedTraceOptions_1785_ = v_inheritedTraceOptions_1696_;
v___y_1786_ = v_a_1655_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1797_; lean_object* v_env_1798_; lean_object* v_nextMacroScope_1799_; lean_object* v_ngen_1800_; lean_object* v_auxDeclNGen_1801_; lean_object* v_traceState_1802_; lean_object* v_messages_1803_; lean_object* v_infoState_1804_; lean_object* v_snapshotTasks_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1815_; 
v___x_1797_ = lean_st_ref_take(v_a_1655_);
v_env_1798_ = lean_ctor_get(v___x_1797_, 0);
v_nextMacroScope_1799_ = lean_ctor_get(v___x_1797_, 1);
v_ngen_1800_ = lean_ctor_get(v___x_1797_, 2);
v_auxDeclNGen_1801_ = lean_ctor_get(v___x_1797_, 3);
v_traceState_1802_ = lean_ctor_get(v___x_1797_, 4);
v_messages_1803_ = lean_ctor_get(v___x_1797_, 6);
v_infoState_1804_ = lean_ctor_get(v___x_1797_, 7);
v_snapshotTasks_1805_ = lean_ctor_get(v___x_1797_, 8);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v___x_1797_, 5);
lean_dec(v_unused_1816_);
v___x_1807_ = v___x_1797_;
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_snapshotTasks_1805_);
lean_inc(v_infoState_1804_);
lean_inc(v_messages_1803_);
lean_inc(v_traceState_1802_);
lean_inc(v_auxDeclNGen_1801_);
lean_inc(v_ngen_1800_);
lean_inc(v_nextMacroScope_1799_);
lean_inc(v_env_1798_);
lean_dec(v___x_1797_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1809_ = l_Lean_Kernel_enableDiag(v_env_1798_, v___x_1771_);
v___x_1810_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 5, v___x_1810_);
lean_ctor_set(v___x_1807_, 0, v___x_1809_);
v___x_1812_ = v___x_1807_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_nextMacroScope_1799_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_ngen_1800_);
lean_ctor_set(v_reuseFailAlloc_1814_, 3, v_auxDeclNGen_1801_);
lean_ctor_set(v_reuseFailAlloc_1814_, 4, v_traceState_1802_);
lean_ctor_set(v_reuseFailAlloc_1814_, 5, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1814_, 6, v_messages_1803_);
lean_ctor_set(v_reuseFailAlloc_1814_, 7, v_infoState_1804_);
lean_ctor_set(v_reuseFailAlloc_1814_, 8, v_snapshotTasks_1805_);
v___x_1812_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_st_ref_set(v_a_1655_, v___x_1812_);
v_fileName_1773_ = v_fileName_1683_;
v_fileMap_1774_ = v_fileMap_1684_;
v_currRecDepth_1775_ = v_currRecDepth_1686_;
v_ref_1776_ = v_ref_1687_;
v_currNamespace_1777_ = v_currNamespace_1688_;
v_openDecls_1778_ = v_openDecls_1689_;
v_initHeartbeats_1779_ = v_initHeartbeats_1690_;
v_maxHeartbeats_1780_ = v_maxHeartbeats_1691_;
v_quotContext_1781_ = v_quotContext_1692_;
v_currMacroScope_1782_ = v_currMacroScope_1693_;
v_cancelTk_x3f_1783_ = v_cancelTk_x3f_1694_;
v_suppressElabErrors_1784_ = v_suppressElabErrors_1695_;
v_inheritedTraceOptions_1785_ = v_inheritedTraceOptions_1696_;
v___y_1786_ = v_a_1655_;
goto v___jp_1772_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1819_; uint8_t v___y_1821_; uint8_t v___x_1830_; 
lean_dec_ref(v___x_1657_);
v_a_1819_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1819_);
v___x_1830_ = l_Lean_Exception_isInterrupt(v_a_1819_);
if (v___x_1830_ == 0)
{
uint8_t v___x_1831_; 
v___x_1831_ = l_Lean_Exception_isRuntime(v_a_1819_);
v___y_1821_ = v___x_1831_;
goto v___jp_1820_;
}
else
{
lean_dec(v_a_1819_);
v___y_1821_ = v___x_1830_;
goto v___jp_1820_;
}
v___jp_1820_:
{
if (v___y_1821_ == 0)
{
lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v___x_1670_, 0);
lean_dec(v_unused_1829_);
v___x_1823_ = v___x_1670_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_dec(v___x_1670_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set_tag(v___x_1823_, 0);
lean_ctor_set(v___x_1823_, 0, v_a_1659_);
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1659_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
else
{
lean_dec(v_a_1659_);
return v___x_1670_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1657_);
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___boxed(lean_object* v_type_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Compiler_LCNF_toLCNFType(v_type_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(lean_object* v_00_u03b2_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1841_, v_x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___boxed(lean_object* v_00_u03b2_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(v_00_u03b2_1844_, v_x_1845_, v_x_1846_);
lean_dec(v_x_1846_);
lean_dec_ref(v_x_1845_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(lean_object* v_00_u03b2_1848_, lean_object* v_m_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___boxed(lean_object* v_00_u03b2_1851_, lean_object* v_m_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(v_00_u03b2_1851_, v_m_1852_);
lean_dec_ref(v_m_1852_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(lean_object* v_00_u03b2_1854_, lean_object* v_x_1855_, size_t v_x_1856_, lean_object* v_x_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1855_, v_x_1856_, v_x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_){
_start:
{
size_t v_x_18768__boxed_1863_; lean_object* v_res_1864_; 
v_x_18768__boxed_1863_ = lean_unbox_usize(v_x_1861_);
lean_dec(v_x_1861_);
v_res_1864_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(v_00_u03b2_1859_, v_x_1860_, v_x_18768__boxed_1863_, v_x_1862_);
lean_dec(v_x_1862_);
lean_dec_ref(v_x_1860_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(lean_object* v_00_u03c3_1865_, lean_object* v_00_u03b2_1866_, lean_object* v_map_1867_, lean_object* v_f_1868_, lean_object* v_init_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_1867_, v_f_1868_, v_init_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_map_1873_, lean_object* v_f_1874_, lean_object* v_init_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(v_00_u03c3_1871_, v_00_u03b2_1872_, v_map_1873_, v_f_1874_, v_init_1875_);
lean_dec_ref(v_map_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1877_, lean_object* v_keys_1878_, lean_object* v_vals_1879_, lean_object* v_heq_1880_, lean_object* v_i_1881_, lean_object* v_k_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_keys_1878_, v_vals_1879_, v_i_1881_, v_k_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1884_, lean_object* v_keys_1885_, lean_object* v_vals_1886_, lean_object* v_heq_1887_, lean_object* v_i_1888_, lean_object* v_k_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(v_00_u03b2_1884_, v_keys_1885_, v_vals_1886_, v_heq_1887_, v_i_1888_, v_k_1889_);
lean_dec(v_k_1889_);
lean_dec_ref(v_vals_1886_);
lean_dec_ref(v_keys_1885_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(lean_object* v_map_1891_, lean_object* v_f_1892_, lean_object* v_init_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1892_, v_map_1891_, v_init_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_map_1895_, lean_object* v_f_1896_, lean_object* v_init_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(v_map_1895_, v_f_1896_, v_init_1897_);
lean_dec_ref(v_map_1895_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(lean_object* v_00_u03c3_1899_, lean_object* v_00_u03b2_1900_, lean_object* v_map_1901_, lean_object* v_f_1902_, lean_object* v_init_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1902_, v_map_1901_, v_init_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03c3_1905_, lean_object* v_00_u03b2_1906_, lean_object* v_map_1907_, lean_object* v_f_1908_, lean_object* v_init_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(v_00_u03c3_1905_, v_00_u03b2_1906_, v_map_1907_, v_f_1908_, v_init_1909_);
lean_dec_ref(v_map_1907_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(lean_object* v_00_u03c3_1911_, lean_object* v_00_u03b1_1912_, lean_object* v_00_u03b2_1913_, lean_object* v_f_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1914_, v_x_1915_, v_x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03c3_1918_, lean_object* v_00_u03b1_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_f_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(v_00_u03c3_1918_, v_00_u03b1_1919_, v_00_u03b2_1920_, v_f_1921_, v_x_1922_, v_x_1923_);
lean_dec_ref(v_x_1922_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(lean_object* v_00_u03b1_1925_, lean_object* v_00_u03b2_1926_, lean_object* v_00_u03c3_1927_, lean_object* v_f_1928_, lean_object* v_as_1929_, size_t v_i_1930_, size_t v_stop_1931_, lean_object* v_b_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1928_, v_as_1929_, v_i_1930_, v_stop_1931_, v_b_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___boxed(lean_object* v_00_u03b1_1934_, lean_object* v_00_u03b2_1935_, lean_object* v_00_u03c3_1936_, lean_object* v_f_1937_, lean_object* v_as_1938_, lean_object* v_i_1939_, lean_object* v_stop_1940_, lean_object* v_b_1941_){
_start:
{
size_t v_i_boxed_1942_; size_t v_stop_boxed_1943_; lean_object* v_res_1944_; 
v_i_boxed_1942_ = lean_unbox_usize(v_i_1939_);
lean_dec(v_i_1939_);
v_stop_boxed_1943_ = lean_unbox_usize(v_stop_1940_);
lean_dec(v_stop_1940_);
v_res_1944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(v_00_u03b1_1934_, v_00_u03b2_1935_, v_00_u03c3_1936_, v_f_1937_, v_as_1938_, v_i_boxed_1942_, v_stop_boxed_1943_, v_b_1941_);
lean_dec_ref(v_as_1938_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(lean_object* v_00_u03c3_1945_, lean_object* v_00_u03b1_1946_, lean_object* v_00_u03b2_1947_, lean_object* v_f_1948_, lean_object* v_keys_1949_, lean_object* v_vals_1950_, lean_object* v_heq_1951_, lean_object* v_i_1952_, lean_object* v_acc_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1948_, v_keys_1949_, v_vals_1950_, v_i_1952_, v_acc_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___boxed(lean_object* v_00_u03c3_1955_, lean_object* v_00_u03b1_1956_, lean_object* v_00_u03b2_1957_, lean_object* v_f_1958_, lean_object* v_keys_1959_, lean_object* v_vals_1960_, lean_object* v_heq_1961_, lean_object* v_i_1962_, lean_object* v_acc_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(v_00_u03c3_1955_, v_00_u03b1_1956_, v_00_u03b2_1957_, v_f_1958_, v_keys_1959_, v_vals_1960_, v_heq_1961_, v_i_1962_, v_acc_1963_);
lean_dec_ref(v_vals_1960_);
lean_dec_ref(v_keys_1959_);
return v_res_1964_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f(lean_object* v_a_1969_, lean_object* v_b_1970_){
_start:
{
lean_object* v___y_1972_; lean_object* v___y_1977_; lean_object* v___y_1978_; uint8_t v___y_1979_; uint8_t v___y_2044_; uint8_t v___x_2054_; 
v___x_2054_ = l_Lean_Expr_isErased(v_a_1969_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Lean_Expr_isErased(v_b_1970_);
v___y_2044_ = v___x_2055_;
goto v___jp_2043_;
}
else
{
v___y_2044_ = v___x_2054_;
goto v___jp_2043_;
}
v___jp_1971_:
{
if (lean_obj_tag(v___y_1972_) == 0)
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1973_;
}
else
{
return v___y_1972_;
}
}
v___jp_1974_:
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1975_;
}
v___jp_1976_:
{
if (v___y_1979_ == 0)
{
lean_dec_ref(v___y_1978_);
lean_dec_ref(v___y_1977_);
switch(lean_obj_tag(v_a_1969_))
{
case 10:
{
lean_object* v_expr_1980_; 
v_expr_1980_ = lean_ctor_get(v_a_1969_, 1);
lean_inc_ref(v_expr_1980_);
lean_dec_ref_known(v_a_1969_, 2);
v_a_1969_ = v_expr_1980_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_1970_))
{
case 10:
{
lean_object* v_expr_1982_; 
v_expr_1982_ = lean_ctor_get(v_b_1970_, 1);
lean_inc_ref(v_expr_1982_);
lean_dec_ref_known(v_b_1970_, 2);
v_b_1970_ = v_expr_1982_;
goto _start;
}
case 5:
{
lean_object* v_fn_1984_; lean_object* v_arg_1985_; lean_object* v_fn_1986_; lean_object* v_arg_1987_; lean_object* v___x_1988_; 
v_fn_1984_ = lean_ctor_get(v_a_1969_, 0);
lean_inc_ref(v_fn_1984_);
v_arg_1985_ = lean_ctor_get(v_a_1969_, 1);
lean_inc_ref(v_arg_1985_);
lean_dec_ref_known(v_a_1969_, 2);
v_fn_1986_ = lean_ctor_get(v_b_1970_, 0);
lean_inc_ref(v_fn_1986_);
v_arg_1987_ = lean_ctor_get(v_b_1970_, 1);
lean_inc_ref(v_arg_1987_);
lean_dec_ref_known(v_b_1970_, 2);
v___x_1988_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_fn_1984_, v_fn_1986_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_dec_ref(v_arg_1987_);
lean_dec_ref(v_arg_1985_);
v___y_1972_ = v___x_1988_;
goto v___jp_1971_;
}
else
{
lean_object* v_val_1989_; lean_object* v___x_1990_; 
v_val_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_val_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_arg_1985_, v_arg_1987_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_dec(v_val_1989_);
v___y_1972_ = v___x_1990_;
goto v___jp_1971_;
}
else
{
lean_object* v_val_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1999_; 
v_val_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_1999_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_val_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1999_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1995_ = l_Lean_Expr_app___override(v_val_1989_, v_val_1991_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1995_);
v___x_1997_ = v___x_1993_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_1969_, 2);
lean_dec_ref(v_b_1970_);
goto v___jp_1974_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_1970_))
{
case 10:
{
lean_object* v_expr_2000_; 
v_expr_2000_ = lean_ctor_get(v_b_1970_, 1);
lean_inc_ref(v_expr_2000_);
lean_dec_ref_known(v_b_1970_, 2);
v_b_1970_ = v_expr_2000_;
goto _start;
}
case 7:
{
lean_object* v_binderName_2002_; lean_object* v_binderType_2003_; lean_object* v_body_2004_; lean_object* v_binderType_2005_; lean_object* v_body_2006_; lean_object* v___x_2007_; 
v_binderName_2002_ = lean_ctor_get(v_a_1969_, 0);
lean_inc(v_binderName_2002_);
v_binderType_2003_ = lean_ctor_get(v_a_1969_, 1);
lean_inc_ref(v_binderType_2003_);
v_body_2004_ = lean_ctor_get(v_a_1969_, 2);
lean_inc_ref(v_body_2004_);
lean_dec_ref_known(v_a_1969_, 3);
v_binderType_2005_ = lean_ctor_get(v_b_1970_, 1);
lean_inc_ref(v_binderType_2005_);
v_body_2006_ = lean_ctor_get(v_b_1970_, 2);
lean_inc_ref(v_body_2006_);
lean_dec_ref_known(v_b_1970_, 3);
v___x_2007_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_2003_, v_binderType_2005_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_dec_ref(v_body_2006_);
lean_dec_ref(v_body_2004_);
lean_dec(v_binderName_2002_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_2008_;
}
else
{
return v___x_2007_;
}
}
else
{
lean_object* v_val_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2019_; 
v_val_2009_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2011_ = v___x_2007_;
v_isShared_2012_ = v_isSharedCheck_2019_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_val_2009_);
lean_dec(v___x_2007_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2019_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2013_ = l_Lean_Compiler_LCNF_joinTypes(v_body_2004_, v_body_2006_);
v___x_2014_ = 0;
v___x_2015_ = l_Lean_Expr_forallE___override(v_binderName_2002_, v_val_2009_, v___x_2013_, v___x_2014_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2015_);
v___x_2017_ = v___x_2011_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_1969_, 3);
lean_dec_ref(v_b_1970_);
goto v___jp_1974_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_1970_))
{
case 10:
{
lean_object* v_expr_2020_; 
v_expr_2020_ = lean_ctor_get(v_b_1970_, 1);
lean_inc_ref(v_expr_2020_);
lean_dec_ref_known(v_b_1970_, 2);
v_b_1970_ = v_expr_2020_;
goto _start;
}
case 6:
{
lean_object* v_binderName_2022_; lean_object* v_binderType_2023_; lean_object* v_body_2024_; lean_object* v_binderType_2025_; lean_object* v_body_2026_; lean_object* v___x_2027_; 
v_binderName_2022_ = lean_ctor_get(v_a_1969_, 0);
lean_inc(v_binderName_2022_);
v_binderType_2023_ = lean_ctor_get(v_a_1969_, 1);
lean_inc_ref(v_binderType_2023_);
v_body_2024_ = lean_ctor_get(v_a_1969_, 2);
lean_inc_ref(v_body_2024_);
lean_dec_ref_known(v_a_1969_, 3);
v_binderType_2025_ = lean_ctor_get(v_b_1970_, 1);
lean_inc_ref(v_binderType_2025_);
v_body_2026_ = lean_ctor_get(v_b_1970_, 2);
lean_inc_ref(v_body_2026_);
lean_dec_ref_known(v_b_1970_, 3);
v___x_2027_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_2023_, v_binderType_2025_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_dec_ref(v_body_2026_);
lean_dec_ref(v_body_2024_);
lean_dec(v_binderName_2022_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_2028_;
}
else
{
return v___x_2027_;
}
}
else
{
lean_object* v_val_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2039_; 
v_val_2029_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2031_ = v___x_2027_;
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_val_2029_);
lean_dec(v___x_2027_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; uint8_t v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2033_ = l_Lean_Compiler_LCNF_joinTypes(v_body_2024_, v_body_2026_);
v___x_2034_ = 0;
v___x_2035_ = l_Lean_Expr_lam___override(v_binderName_2022_, v_val_2029_, v___x_2033_, v___x_2034_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2035_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
default: 
{
lean_dec_ref_known(v_a_1969_, 3);
lean_dec_ref(v_b_1970_);
goto v___jp_1974_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_1970_) == 10)
{
lean_object* v_expr_2040_; 
v_expr_2040_ = lean_ctor_get(v_b_1970_, 1);
lean_inc_ref(v_expr_2040_);
lean_dec_ref_known(v_b_1970_, 2);
v_b_1970_ = v_expr_2040_;
goto _start;
}
else
{
lean_dec_ref(v_b_1970_);
lean_dec_ref(v_a_1969_);
goto v___jp_1974_;
}
}
}
}
else
{
lean_dec_ref(v_b_1970_);
lean_dec_ref(v_a_1969_);
v_a_1969_ = v___y_1977_;
v_b_1970_ = v___y_1978_;
goto _start;
}
}
v___jp_2043_:
{
if (v___y_2044_ == 0)
{
uint8_t v___x_2045_; 
v___x_2045_ = lean_expr_eqv(v_a_1969_, v_b_1970_);
if (v___x_2045_ == 0)
{
lean_object* v_a_x27_2046_; lean_object* v_b_x27_2047_; uint8_t v___x_2048_; uint8_t v___x_2049_; 
lean_inc_ref(v_a_1969_);
v_a_x27_2046_ = l_Lean_Expr_headBeta(v_a_1969_);
lean_inc_ref(v_b_1970_);
v_b_x27_2047_ = l_Lean_Expr_headBeta(v_b_1970_);
v___x_2048_ = lean_expr_eqv(v_a_1969_, v_a_x27_2046_);
v___x_2049_ = lean_bool_not(v___x_2048_);
if (v___x_2049_ == 0)
{
uint8_t v___x_2050_; uint8_t v___x_2051_; 
v___x_2050_ = lean_expr_eqv(v_b_1970_, v_b_x27_2047_);
v___x_2051_ = lean_bool_not(v___x_2050_);
v___y_1977_ = v_a_x27_2046_;
v___y_1978_ = v_b_x27_2047_;
v___y_1979_ = v___x_2051_;
goto v___jp_1976_;
}
else
{
v___y_1977_ = v_a_x27_2046_;
v___y_1978_ = v_b_x27_2047_;
v___y_1979_ = v___x_2049_;
goto v___jp_1976_;
}
}
else
{
lean_object* v___x_2052_; 
lean_dec_ref(v_b_1970_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_a_1969_);
return v___x_2052_;
}
}
else
{
lean_object* v___x_2053_; 
lean_dec_ref(v_b_1970_);
lean_dec_ref(v_a_1969_);
v___x_2053_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1);
return v___x_2053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object* v_a_2056_, lean_object* v_b_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_a_2056_, v_b_2057_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
return v___x_2059_;
}
else
{
lean_object* v_val_2060_; 
v_val_2060_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_val_2060_);
lean_dec_ref_known(v___x_2058_, 1);
return v_val_2060_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object* v_type_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_Expr_headBeta(v_type_2061_);
switch(lean_obj_tag(v___x_2062_))
{
case 3:
{
uint8_t v___x_2063_; 
lean_dec_ref_known(v___x_2062_, 1);
v___x_2063_ = 1;
return v___x_2063_;
}
case 7:
{
lean_object* v_body_2064_; 
v_body_2064_ = lean_ctor_get(v___x_2062_, 2);
lean_inc_ref(v_body_2064_);
lean_dec_ref_known(v___x_2062_, 3);
v_type_2061_ = v_body_2064_;
goto _start;
}
default: 
{
uint8_t v___x_2066_; 
lean_dec_ref(v___x_2062_);
v___x_2066_ = 0;
return v___x_2066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTypeFormerType___boxed(lean_object* v_type_2067_){
_start:
{
uint8_t v_res_2068_; lean_object* v_r_2069_; 
v_res_2068_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_2067_);
v_r_2069_ = lean_box(v_res_2068_);
return v_r_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(lean_object* v_msgData_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; lean_object* v_env_2075_; lean_object* v_options_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2074_ = lean_st_ref_get(v___y_2072_);
v_env_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc_ref(v_env_2075_);
lean_dec(v___x_2074_);
v_options_2076_ = lean_ctor_get(v___y_2071_, 2);
v___x_2077_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_2078_ = lean_unsigned_to_nat(32u);
v___x_2079_ = lean_mk_empty_array_with_capacity(v___x_2078_);
lean_dec_ref(v___x_2079_);
v___x_2080_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_2076_);
v___x_2081_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2081_, 0, v_env_2075_);
lean_ctor_set(v___x_2081_, 1, v___x_2077_);
lean_ctor_set(v___x_2081_, 2, v___x_2080_);
lean_ctor_set(v___x_2081_, 3, v_options_2076_);
v___x_2082_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v_msgData_2070_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0___boxed(lean_object* v_msgData_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msgData_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(lean_object* v_msg_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_ref_2093_; lean_object* v___x_2094_; lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
v_ref_2093_ = lean_ctor_get(v___y_2090_, 5);
v___x_2094_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msg_2089_, v___y_2090_, v___y_2091_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_inc(v_ref_2093_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v_ref_2093_);
lean_ctor_set(v___x_2099_, 1, v_a_2095_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 1);
lean_ctor_set(v___x_2097_, 0, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg___boxed(lean_object* v_msg_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2108_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0));
v___x_2111_ = l_Lean_stringToMessageData(v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(lean_object* v_ps_2112_, lean_object* v_i_2113_, lean_object* v_type_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = lean_array_get_size(v_ps_2112_);
v___x_2119_ = lean_nat_dec_lt(v_i_2113_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; 
lean_dec(v_i_2113_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v_type_2114_);
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Expr_headBeta(v_type_2114_);
if (lean_obj_tag(v___x_2121_) == 7)
{
lean_object* v_body_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_body_2122_ = lean_ctor_get(v___x_2121_, 2);
lean_inc_ref(v_body_2122_);
lean_dec_ref_known(v___x_2121_, 3);
v___x_2123_ = lean_unsigned_to_nat(1u);
v___x_2124_ = lean_nat_add(v_i_2113_, v___x_2123_);
v___x_2125_ = lean_array_fget_borrowed(v_ps_2112_, v_i_2113_);
lean_dec(v_i_2113_);
v___x_2126_ = lean_expr_instantiate1(v_body_2122_, v___x_2125_);
lean_dec_ref(v_body_2122_);
v_i_2113_ = v___x_2124_;
v_type_2114_ = v___x_2126_;
goto _start;
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec_ref(v___x_2121_);
lean_dec(v_i_2113_);
v___x_2128_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1);
v___x_2129_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v___x_2128_, v_a_2115_, v_a_2116_);
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object* v_ps_2130_, lean_object* v_i_2131_, lean_object* v_type_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2130_, v_i_2131_, v_type_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec_ref(v_ps_2130_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(lean_object* v_00_u03b1_2137_, lean_object* v_msg_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2138_, v___y_2139_, v___y_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___boxed(lean_object* v_00_u03b1_2143_, lean_object* v_msg_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(v_00_u03b1_2143_, v_msg_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter___redArg(lean_object* v_e_2149_, lean_object* v_h__1_2150_, lean_object* v_h__2_2151_){
_start:
{
if (lean_obj_tag(v_e_2149_) == 7)
{
lean_object* v_binderName_2152_; lean_object* v_binderType_2153_; lean_object* v_body_2154_; uint8_t v_binderInfo_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec(v_h__2_2151_);
v_binderName_2152_ = lean_ctor_get(v_e_2149_, 0);
lean_inc(v_binderName_2152_);
v_binderType_2153_ = lean_ctor_get(v_e_2149_, 1);
lean_inc_ref(v_binderType_2153_);
v_body_2154_ = lean_ctor_get(v_e_2149_, 2);
lean_inc_ref(v_body_2154_);
v_binderInfo_2155_ = lean_ctor_get_uint8(v_e_2149_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2149_, 3);
v___x_2156_ = lean_box(v_binderInfo_2155_);
v___x_2157_ = lean_apply_4(v_h__1_2150_, v_binderName_2152_, v_binderType_2153_, v_body_2154_, v___x_2156_);
return v___x_2157_;
}
else
{
lean_object* v___x_2158_; 
lean_dec(v_h__1_2150_);
v___x_2158_ = lean_apply_2(v_h__2_2151_, v_e_2149_, lean_box(0));
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter(lean_object* v_motive_2159_, lean_object* v_e_2160_, lean_object* v_h__1_2161_, lean_object* v_h__2_2162_){
_start:
{
if (lean_obj_tag(v_e_2160_) == 7)
{
lean_object* v_binderName_2163_; lean_object* v_binderType_2164_; lean_object* v_body_2165_; uint8_t v_binderInfo_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec(v_h__2_2162_);
v_binderName_2163_ = lean_ctor_get(v_e_2160_, 0);
lean_inc(v_binderName_2163_);
v_binderType_2164_ = lean_ctor_get(v_e_2160_, 1);
lean_inc_ref(v_binderType_2164_);
v_body_2165_ = lean_ctor_get(v_e_2160_, 2);
lean_inc_ref(v_body_2165_);
v_binderInfo_2166_ = lean_ctor_get_uint8(v_e_2160_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2160_, 3);
v___x_2167_ = lean_box(v_binderInfo_2166_);
v___x_2168_ = lean_apply_4(v_h__1_2161_, v_binderName_2163_, v_binderType_2164_, v_body_2165_, v___x_2167_);
return v___x_2168_;
}
else
{
lean_object* v___x_2169_; 
lean_dec(v_h__1_2161_);
v___x_2169_ = lean_apply_2(v_h__2_2162_, v_e_2160_, lean_box(0));
return v___x_2169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object* v_type_2170_, lean_object* v_ps_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2171_, v___x_2175_, v_type_2170_, v_a_2172_, v_a_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object* v_type_2177_, lean_object* v_ps_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_2177_, v_ps_2178_, v_a_2179_, v_a_2180_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec_ref(v_ps_2178_);
return v_res_2182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object* v_type_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_Expr_headBeta(v_type_2183_);
switch(lean_obj_tag(v___x_2184_))
{
case 3:
{
lean_object* v_u_2185_; 
v_u_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_u_2185_);
lean_dec_ref_known(v___x_2184_, 1);
if (lean_obj_tag(v_u_2185_) == 0)
{
uint8_t v___x_2186_; 
v___x_2186_ = 1;
return v___x_2186_;
}
else
{
uint8_t v___x_2187_; 
lean_dec(v_u_2185_);
v___x_2187_ = 0;
return v___x_2187_;
}
}
case 7:
{
lean_object* v_body_2188_; 
v_body_2188_ = lean_ctor_get(v___x_2184_, 2);
lean_inc_ref(v_body_2188_);
lean_dec_ref_known(v___x_2184_, 3);
v_type_2183_ = v_body_2188_;
goto _start;
}
default: 
{
uint8_t v___x_2190_; 
lean_dec_ref(v___x_2184_);
v___x_2190_ = 0;
return v___x_2190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPredicateType___boxed(lean_object* v_type_2191_){
_start:
{
uint8_t v_res_2192_; lean_object* v_r_2193_; 
v_res_2192_ = l_Lean_Compiler_LCNF_isPredicateType(v_type_2191_);
v_r_2193_ = lean_box(v_res_2192_);
return v_r_2193_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_maybeTypeFormerType(lean_object* v_type_2194_){
_start:
{
lean_object* v___x_2195_; 
lean_inc_ref(v_type_2194_);
v___x_2195_ = l_Lean_Expr_headBeta(v_type_2194_);
switch(lean_obj_tag(v___x_2195_))
{
case 3:
{
uint8_t v___x_2196_; 
lean_dec_ref_known(v___x_2195_, 1);
lean_dec_ref(v_type_2194_);
v___x_2196_ = 1;
return v___x_2196_;
}
case 7:
{
lean_object* v_body_2197_; 
lean_dec_ref(v_type_2194_);
v_body_2197_ = lean_ctor_get(v___x_2195_, 2);
lean_inc_ref(v_body_2197_);
lean_dec_ref_known(v___x_2195_, 3);
v_type_2194_ = v_body_2197_;
goto _start;
}
default: 
{
uint8_t v___x_2199_; 
lean_dec_ref(v___x_2195_);
v___x_2199_ = l_Lean_Expr_isErased(v_type_2194_);
lean_dec_ref(v_type_2194_);
return v___x_2199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_maybeTypeFormerType___boxed(lean_object* v_type_2200_){
_start:
{
uint8_t v_res_2201_; lean_object* v_r_2202_; 
v_res_2201_ = l_Lean_Compiler_LCNF_maybeTypeFormerType(v_type_2200_);
v_r_2202_ = lean_box(v_res_2201_);
return v_r_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object* v_type_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Expr_getAppFn(v_type_2203_);
if (lean_obj_tag(v___x_2206_) == 4)
{
lean_object* v_declName_2207_; lean_object* v___x_2208_; lean_object* v_env_2209_; uint8_t v___x_2210_; 
v_declName_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_declName_2207_);
lean_dec_ref_known(v___x_2206_, 2);
v___x_2208_ = lean_st_ref_get(v_a_2204_);
v_env_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc_ref(v_env_2209_);
lean_dec(v___x_2208_);
v___x_2210_ = l_Lean_isClass(v_env_2209_, v_declName_2207_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_dec(v_declName_2207_);
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
return v___x_2212_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_declName_2207_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec_ref(v___x_2206_);
v___x_2215_ = lean_box(0);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg___boxed(lean_object* v_type_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2217_, v_a_2218_);
lean_dec(v_a_2218_);
lean_dec_ref(v_type_2217_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object* v_type_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2221_, v_a_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___boxed(lean_object* v_type_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Compiler_LCNF_isClass_x3f(v_type_2226_, v_a_2227_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec_ref(v_type_2226_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object* v_type_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___x_2234_; 
lean_inc_ref(v_type_2231_);
v___x_2234_ = l_Lean_Expr_headBeta(v_type_2231_);
if (lean_obj_tag(v___x_2234_) == 7)
{
lean_object* v_body_2235_; 
lean_dec_ref(v_type_2231_);
v_body_2235_ = lean_ctor_get(v___x_2234_, 2);
lean_inc_ref(v_body_2235_);
lean_dec_ref_known(v___x_2234_, 3);
v_type_2231_ = v_body_2235_;
goto _start;
}
else
{
lean_object* v___x_2237_; 
lean_dec_ref(v___x_2234_);
v___x_2237_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2231_, v_a_2232_);
lean_dec_ref(v_type_2231_);
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg___boxed(lean_object* v_type_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2238_, v_a_2239_);
lean_dec(v_a_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object* v_type_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2242_, v_a_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___boxed(lean_object* v_type_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Compiler_LCNF_isArrowClass_x3f(v_type_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object* v_e_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Expr_headBeta(v_e_2252_);
if (lean_obj_tag(v___x_2253_) == 7)
{
lean_object* v_body_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v_body_2254_ = lean_ctor_get(v___x_2253_, 2);
lean_inc_ref(v_body_2254_);
lean_dec_ref_known(v___x_2253_, 3);
v___x_2255_ = l_Lean_Compiler_LCNF_getArrowArity(v_body_2254_);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_nat_add(v___x_2255_, v___x_2256_);
lean_dec(v___x_2255_);
return v___x_2257_;
}
else
{
lean_object* v___x_2258_; 
lean_dec_ref(v___x_2253_);
v___x_2258_ = lean_unsigned_to_nat(0u);
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object* v_type_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Expr_getAppFn(v_type_2259_);
if (lean_obj_tag(v___x_2266_) == 4)
{
lean_object* v_declName_2267_; lean_object* v___x_2268_; lean_object* v_env_2269_; uint8_t v___x_2270_; lean_object* v___x_2271_; 
v_declName_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_declName_2267_);
lean_dec_ref_known(v___x_2266_, 2);
v___x_2268_ = lean_st_ref_get(v_a_2260_);
v_env_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc_ref(v_env_2269_);
lean_dec(v___x_2268_);
v___x_2270_ = 0;
v___x_2271_ = l_Lean_Environment_find_x3f(v_env_2269_, v_declName_2267_, v___x_2270_);
if (lean_obj_tag(v___x_2271_) == 1)
{
lean_object* v_val_2272_; 
v_val_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_val_2272_);
lean_dec_ref_known(v___x_2271_, 1);
if (lean_obj_tag(v_val_2272_) == 5)
{
lean_object* v_val_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2284_; 
v_val_2273_ = lean_ctor_get(v_val_2272_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_val_2272_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2275_ = v_val_2272_;
v_isShared_2276_ = v_isSharedCheck_2284_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_val_2273_);
lean_dec(v_val_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2284_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2277_ = l_Lean_InductiveVal_numCtors(v_val_2273_);
lean_dec_ref(v_val_2273_);
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = lean_nat_dec_eq(v___x_2277_, v___x_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(v___x_2279_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set_tag(v___x_2275_, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2280_);
v___x_2282_ = v___x_2275_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
else
{
lean_dec(v_val_2272_);
goto v___jp_2262_;
}
}
else
{
lean_dec(v___x_2271_);
goto v___jp_2262_;
}
}
else
{
uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v___x_2266_);
v___x_2285_ = 0;
v___x_2286_ = lean_box(v___x_2285_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
v___jp_2262_:
{
uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = 0;
v___x_2264_ = lean_box(v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg___boxed(lean_object* v_type_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2288_, v_a_2289_);
lean_dec(v_a_2289_);
lean_dec_ref(v_type_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object* v_type_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2292_, v_a_2294_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___boxed(lean_object* v_type_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors(v_type_2297_, v_a_2298_, v_a_2299_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec_ref(v_type_2297_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object* v_n_2303_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2305_ = l_Lean_Name_str___override(v_n_2303_, v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isBoxedName(lean_object* v_name_2306_){
_start:
{
if (lean_obj_tag(v_name_2306_) == 1)
{
lean_object* v_str_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v_str_2307_ = lean_ctor_get(v_name_2306_, 1);
v___x_2308_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2309_ = lean_string_dec_eq(v_str_2307_, v___x_2308_);
return v___x_2309_;
}
else
{
uint8_t v___x_2310_; 
v___x_2310_ = 0;
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isBoxedName___boxed(lean_object* v_name_2311_){
_start:
{
uint8_t v_res_2312_; lean_object* v_r_2313_; 
v_res_2312_ = l_Lean_Compiler_LCNF_isBoxedName(v_name_2311_);
lean_dec(v_name_2311_);
v_r_2313_ = lean_box(v_res_2312_);
return v_r_2313_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = lean_box(0);
v___x_2318_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__1));
v___x_2319_ = l_Lean_Expr_const___override(v___x_2318_, v___x_2317_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float(void){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2);
return v___x_2320_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_box(0);
v___x_2325_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__1));
v___x_2326_ = l_Lean_Expr_const___override(v___x_2325_, v___x_2324_);
return v___x_2326_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32(void){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = lean_box(0);
v___x_2332_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1));
v___x_2333_ = l_Lean_Expr_const___override(v___x_2332_, v___x_2331_);
return v___x_2333_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8(void){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2);
return v___x_2334_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2338_ = lean_box(0);
v___x_2339_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1));
v___x_2340_ = l_Lean_Expr_const___override(v___x_2339_, v___x_2338_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16(void){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2);
return v___x_2341_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = lean_box(0);
v___x_2346_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1));
v___x_2347_ = l_Lean_Expr_const___override(v___x_2346_, v___x_2345_);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32(void){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2);
return v___x_2348_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2352_ = lean_box(0);
v___x_2353_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1));
v___x_2354_ = l_Lean_Expr_const___override(v___x_2353_, v___x_2352_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64(void){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2);
return v___x_2355_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_box(0);
v___x_2360_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__1));
v___x_2361_ = l_Lean_Expr_const___override(v___x_2360_, v___x_2359_);
return v___x_2361_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize(void){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_usize___closed__2, &l_Lean_Compiler_LCNF_ImpureType_usize___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2);
return v___x_2362_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = lean_box(0);
v___x_2364_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_2365_ = l_Lean_Expr_const___override(v___x_2364_, v___x_2363_);
return v___x_2365_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased(void){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_erased___closed__0, &l_Lean_Compiler_LCNF_ImpureType_erased___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0);
return v___x_2366_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2370_ = lean_box(0);
v___x_2371_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__1));
v___x_2372_ = l_Lean_Expr_const___override(v___x_2371_, v___x_2370_);
return v___x_2372_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object(void){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2373_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = lean_box(0);
v___x_2378_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1));
v___x_2379_ = l_Lean_Expr_const___override(v___x_2378_, v___x_2377_);
return v___x_2379_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject(void){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = lean_box(0);
v___x_2385_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1));
v___x_2386_ = l_Lean_Expr_const___override(v___x_2385_, v___x_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged(void){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = lean_box(0);
v___x_2389_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_2390_ = l_Lean_Expr_const___override(v___x_2389_, v___x_2388_);
return v___x_2390_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void(void){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_void___closed__0, &l_Lean_Compiler_LCNF_ImpureType_void___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0);
return v___x_2391_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object* v_x_2392_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 4)
{
lean_object* v_declName_2393_; 
v_declName_2393_ = lean_ctor_get(v_x_2392_, 0);
if (lean_obj_tag(v_declName_2393_) == 1)
{
lean_object* v_pre_2394_; 
v_pre_2394_ = lean_ctor_get(v_declName_2393_, 0);
if (lean_obj_tag(v_pre_2394_) == 0)
{
lean_object* v_us_2395_; lean_object* v_str_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
v_us_2395_ = lean_ctor_get(v_x_2392_, 1);
v_str_2396_ = lean_ctor_get(v_declName_2393_, 1);
v___x_2397_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2398_ = lean_string_dec_eq(v_str_2396_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2400_ = lean_string_dec_eq(v_str_2396_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2402_ = lean_string_dec_eq(v_str_2396_, v___x_2401_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2404_ = lean_string_dec_eq(v_str_2396_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0));
v___x_2406_ = lean_string_dec_eq(v_str_2396_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2408_ = lean_string_dec_eq(v_str_2396_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__0));
v___x_2410_ = lean_string_dec_eq(v_str_2396_, v___x_2409_);
if (v___x_2410_ == 0)
{
return v___x_2410_;
}
else
{
if (lean_obj_tag(v_us_2395_) == 0)
{
return v___x_2410_;
}
else
{
return v___x_2408_;
}
}
}
else
{
if (lean_obj_tag(v_us_2395_) == 0)
{
return v___x_2408_;
}
else
{
return v___x_2406_;
}
}
}
else
{
if (lean_obj_tag(v_us_2395_) == 0)
{
return v___x_2406_;
}
else
{
return v___x_2404_;
}
}
}
else
{
if (lean_obj_tag(v_us_2395_) == 0)
{
return v___x_2404_;
}
else
{
return v___x_2402_;
}
}
}
else
{
if (lean_obj_tag(v_us_2395_) == 0)
{
return v___x_2402_;
}
else
{
return v___x_2400_;
}
}
}
else
{
if (lean_obj_tag(v_us_2395_) == 0)
{
return v___x_2400_;
}
else
{
return v___x_2398_;
}
}
}
else
{
if (lean_obj_tag(v_us_2395_) == 0)
{
return v___x_2398_;
}
else
{
uint8_t v___x_2411_; 
v___x_2411_ = 0;
return v___x_2411_;
}
}
}
else
{
uint8_t v___x_2412_; 
v___x_2412_ = 0;
return v___x_2412_;
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar___boxed(lean_object* v_x_2415_){
_start:
{
uint8_t v_res_2416_; lean_object* v_r_2417_; 
v_res_2416_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_x_2415_);
lean_dec_ref(v_x_2415_);
v_r_2417_ = lean_box(v_res_2416_);
return v_r_2417_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(lean_object* v_x_2418_){
_start:
{
if (lean_obj_tag(v_x_2418_) == 4)
{
lean_object* v_declName_2419_; 
v_declName_2419_ = lean_ctor_get(v_x_2418_, 0);
if (lean_obj_tag(v_declName_2419_) == 1)
{
lean_object* v_pre_2420_; 
v_pre_2420_ = lean_ctor_get(v_declName_2419_, 0);
if (lean_obj_tag(v_pre_2420_) == 0)
{
lean_object* v_us_2421_; lean_object* v_str_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_us_2421_ = lean_ctor_get(v_x_2418_, 1);
v_str_2422_ = lean_ctor_get(v_declName_2419_, 1);
v___x_2423_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2424_ = lean_string_dec_eq(v_str_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2426_ = lean_string_dec_eq(v_str_2422_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2427_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2428_ = lean_string_dec_eq(v_str_2422_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2430_ = lean_string_dec_eq(v_str_2422_, v___x_2429_);
if (v___x_2430_ == 0)
{
return v___x_2430_;
}
else
{
if (lean_obj_tag(v_us_2421_) == 0)
{
return v___x_2430_;
}
else
{
return v___x_2428_;
}
}
}
else
{
if (lean_obj_tag(v_us_2421_) == 0)
{
return v___x_2428_;
}
else
{
return v___x_2426_;
}
}
}
else
{
if (lean_obj_tag(v_us_2421_) == 0)
{
return v___x_2426_;
}
else
{
return v___x_2424_;
}
}
}
else
{
if (lean_obj_tag(v_us_2421_) == 0)
{
return v___x_2424_;
}
else
{
uint8_t v___x_2431_; 
v___x_2431_ = 0;
return v___x_2431_;
}
}
}
else
{
uint8_t v___x_2432_; 
v___x_2432_ = 0;
return v___x_2432_;
}
}
else
{
uint8_t v___x_2433_; 
v___x_2433_ = 0;
return v___x_2433_;
}
}
else
{
uint8_t v___x_2434_; 
v___x_2434_ = 0;
return v___x_2434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj___boxed(lean_object* v_x_2435_){
_start:
{
uint8_t v_res_2436_; lean_object* v_r_2437_; 
v_res_2436_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(v_x_2435_);
lean_dec_ref(v_x_2435_);
v_r_2437_ = lean_box(v_res_2436_);
return v_r_2437_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object* v_x_2438_){
_start:
{
if (lean_obj_tag(v_x_2438_) == 4)
{
lean_object* v_declName_2439_; 
v_declName_2439_ = lean_ctor_get(v_x_2438_, 0);
if (lean_obj_tag(v_declName_2439_) == 1)
{
lean_object* v_pre_2440_; 
v_pre_2440_ = lean_ctor_get(v_declName_2439_, 0);
if (lean_obj_tag(v_pre_2440_) == 0)
{
lean_object* v_us_2441_; lean_object* v_str_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v_us_2441_ = lean_ctor_get(v_x_2438_, 1);
v_str_2442_ = lean_ctor_get(v_declName_2439_, 1);
v___x_2443_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2444_ = lean_string_dec_eq(v_str_2442_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2445_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2446_ = lean_string_dec_eq(v_str_2442_, v___x_2445_);
if (v___x_2446_ == 0)
{
return v___x_2446_;
}
else
{
if (lean_obj_tag(v_us_2441_) == 0)
{
return v___x_2446_;
}
else
{
return v___x_2444_;
}
}
}
else
{
if (lean_obj_tag(v_us_2441_) == 0)
{
return v___x_2444_;
}
else
{
uint8_t v___x_2447_; 
v___x_2447_ = 0;
return v___x_2447_;
}
}
}
else
{
uint8_t v___x_2448_; 
v___x_2448_ = 0;
return v___x_2448_;
}
}
else
{
uint8_t v___x_2449_; 
v___x_2449_ = 0;
return v___x_2449_;
}
}
else
{
uint8_t v___x_2450_; 
v___x_2450_ = 0;
return v___x_2450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef___boxed(lean_object* v_x_2451_){
_start:
{
uint8_t v_res_2452_; lean_object* v_r_2453_; 
v_res_2452_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_x_2451_);
lean_dec_ref(v_x_2451_);
v_r_2453_ = lean_box(v_res_2452_);
return v_r_2453_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(lean_object* v_x_2454_){
_start:
{
if (lean_obj_tag(v_x_2454_) == 4)
{
lean_object* v_declName_2455_; 
v_declName_2455_ = lean_ctor_get(v_x_2454_, 0);
if (lean_obj_tag(v_declName_2455_) == 1)
{
lean_object* v_pre_2456_; 
v_pre_2456_ = lean_ctor_get(v_declName_2455_, 0);
if (lean_obj_tag(v_pre_2456_) == 0)
{
lean_object* v_us_2457_; lean_object* v_str_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v_us_2457_ = lean_ctor_get(v_x_2454_, 1);
v_str_2458_ = lean_ctor_get(v_declName_2455_, 1);
v___x_2459_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2460_ = lean_string_dec_eq(v_str_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
return v___x_2460_;
}
else
{
if (lean_obj_tag(v_us_2457_) == 0)
{
return v___x_2460_;
}
else
{
uint8_t v___x_2461_; 
v___x_2461_ = 0;
return v___x_2461_;
}
}
}
else
{
uint8_t v___x_2462_; 
v___x_2462_ = 0;
return v___x_2462_;
}
}
else
{
uint8_t v___x_2463_; 
v___x_2463_ = 0;
return v___x_2463_;
}
}
else
{
uint8_t v___x_2464_; 
v___x_2464_ = 0;
return v___x_2464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef___boxed(lean_object* v_x_2465_){
_start:
{
uint8_t v_res_2466_; lean_object* v_r_2467_; 
v_res_2466_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_x_2465_);
lean_dec_ref(v_x_2465_);
v_r_2467_ = lean_box(v_res_2466_);
return v_r_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object* v_x_2468_){
_start:
{
if (lean_obj_tag(v_x_2468_) == 4)
{
lean_object* v_declName_2475_; 
v_declName_2475_ = lean_ctor_get(v_x_2468_, 0);
if (lean_obj_tag(v_declName_2475_) == 1)
{
lean_object* v_pre_2476_; 
v_pre_2476_ = lean_ctor_get(v_declName_2475_, 0);
if (lean_obj_tag(v_pre_2476_) == 0)
{
lean_object* v_us_2477_; lean_object* v_str_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v_us_2477_ = lean_ctor_get(v_x_2468_, 1);
v_str_2478_ = lean_ctor_get(v_declName_2475_, 1);
v___x_2479_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2480_ = lean_string_dec_eq(v_str_2478_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2481_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2482_ = lean_string_dec_eq(v_str_2478_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2483_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2484_ = lean_string_dec_eq(v_str_2478_, v___x_2483_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2486_ = lean_string_dec_eq(v_str_2478_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2487_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2488_ = lean_string_dec_eq(v_str_2478_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2490_ = lean_string_dec_eq(v_str_2478_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2491_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2492_ = lean_string_dec_eq(v_str_2478_, v___x_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2494_ = lean_string_dec_eq(v_str_2478_, v___x_2493_);
if (v___x_2494_ == 0)
{
goto v___jp_2469_;
}
else
{
if (lean_obj_tag(v_us_2477_) == 0)
{
goto v___jp_2473_;
}
else
{
goto v___jp_2469_;
}
}
}
else
{
if (lean_obj_tag(v_us_2477_) == 0)
{
goto v___jp_2473_;
}
else
{
goto v___jp_2469_;
}
}
}
else
{
if (lean_obj_tag(v_us_2477_) == 0)
{
goto v___jp_2473_;
}
else
{
goto v___jp_2469_;
}
}
}
else
{
if (lean_obj_tag(v_us_2477_) == 0)
{
goto v___jp_2473_;
}
else
{
goto v___jp_2469_;
}
}
}
else
{
if (lean_obj_tag(v_us_2477_) == 0)
{
goto v___jp_2471_;
}
else
{
goto v___jp_2469_;
}
}
}
else
{
if (lean_obj_tag(v_us_2477_) == 0)
{
goto v___jp_2471_;
}
else
{
goto v___jp_2469_;
}
}
}
else
{
if (lean_obj_tag(v_us_2477_) == 0)
{
goto v___jp_2471_;
}
else
{
goto v___jp_2469_;
}
}
}
else
{
if (lean_obj_tag(v_us_2477_) == 0)
{
goto v___jp_2471_;
}
else
{
goto v___jp_2469_;
}
}
}
else
{
goto v___jp_2469_;
}
}
else
{
goto v___jp_2469_;
}
}
else
{
goto v___jp_2469_;
}
v___jp_2469_:
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2470_;
}
v___jp_2471_:
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2472_;
}
v___jp_2473_:
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed___boxed(lean_object* v_x_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_x_2495_);
lean_dec_ref(v_x_2495_);
return v_res_2496_;
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
