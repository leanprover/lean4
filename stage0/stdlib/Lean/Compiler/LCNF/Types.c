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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
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
uint8_t lean_is_class(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1;
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
lean_dec_ref(v_a_28_);
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
lean_inc(v_quotContext_34_);
v_currMacroScope_35_ = lean_ctor_get(v_a_28_, 2);
lean_inc(v_currMacroScope_35_);
v_ref_36_ = lean_ctor_get(v_a_28_, 5);
lean_inc(v_ref_36_);
lean_dec_ref(v_a_28_);
v___x_37_ = 0;
v___x_38_ = l_Lean_SourceInfo_fromRef(v_ref_36_, v___x_37_);
lean_dec(v_ref_36_);
v___x_39_ = lean_obj_once(&l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1, &l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1_once, _init_l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1);
v___x_40_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
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
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1(lean_object* v_x_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__1));
lean_inc(v_x_48_);
v___x_52_ = l_Lean_Syntax_isOfKind(v_x_48_, v___x_51_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_x_48_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v_a_50_);
return v___x_54_;
}
else
{
lean_object* v_ref_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_ref_55_ = l_Lean_replaceRef(v_x_48_, v_a_49_);
lean_dec(v_x_48_);
v___x_56_ = 0;
v___x_57_ = l_Lean_SourceInfo_fromRef(v_ref_55_, v___x_56_);
lean_dec(v_ref_55_);
v___x_58_ = ((lean_object*)(l_Lean_Compiler_term_u25fe___closed__3));
v___x_59_ = ((lean_object*)(l_Lean_Compiler_term_u25fe___closed__4));
lean_inc(v___x_57_);
v___x_60_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_57_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = l_Lean_Syntax_node1(v___x_57_, v___x_58_, v___x_60_);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v_a_50_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___boxed(lean_object* v_x_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1(v_x_63_, v_a_64_, v_a_65_);
lean_dec(v_a_64_);
return v_res_66_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_erasedExpr___closed__0(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_box(0);
v___x_68_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_69_ = l_Lean_mkConst(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_erasedExpr(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_obj_once(&l_Lean_Compiler_LCNF_erasedExpr___closed__0, &l_Lean_Compiler_LCNF_erasedExpr___closed__0_once, _init_l_Lean_Compiler_LCNF_erasedExpr___closed__0);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_anyExpr___closed__2(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_box(0);
v___x_75_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyExpr___closed__1));
v___x_76_ = l_Lean_mkConst(v___x_75_, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_anyExpr(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
return v___x_77_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isVoid(lean_object* v_e_81_){
_start:
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_83_ = l_Lean_Expr_isAppOf(v_e_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isVoid___boxed(lean_object* v_e_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Lean_Expr_isVoid(v_e_84_);
lean_dec_ref(v_e_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isErased(lean_object* v_e_87_){
_start:
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_89_ = l_Lean_Expr_isAppOf(v_e_87_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isErased___boxed(lean_object* v_e_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Lean_Expr_isErased(v_e_90_);
lean_dec_ref(v_e_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAny(lean_object* v_e_93_){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lean_Compiler_LCNF_anyExpr___closed__1));
v___x_95_ = l_Lean_Expr_isAppOf(v_e_93_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAny___boxed(lean_object* v_e_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Lean_Expr_isAny(v_e_96_);
lean_dec_ref(v_e_96_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPropFormerTypeQuick(lean_object* v_x_99_){
_start:
{
switch(lean_obj_tag(v_x_99_))
{
case 7:
{
lean_object* v_body_100_; 
v_body_100_ = lean_ctor_get(v_x_99_, 2);
v_x_99_ = v_body_100_;
goto _start;
}
case 3:
{
lean_object* v_u_102_; 
v_u_102_ = lean_ctor_get(v_x_99_, 0);
if (lean_obj_tag(v_u_102_) == 0)
{
uint8_t v___x_103_; 
v___x_103_ = 1;
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
default: 
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerTypeQuick___boxed(lean_object* v_x_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_x_106_);
lean_dec_ref(v_x_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(lean_object* v_k_109_, lean_object* v_b_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_apply_6(v_k_109_, v_b_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, lean_box(0));
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_117_, lean_object* v_b_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(v_k_117_, v_b_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(lean_object* v_name_125_, uint8_t v_bi_126_, lean_object* v_type_127_, lean_object* v_k_128_, uint8_t v_kind_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___f_135_; lean_object* v___x_136_; 
v___f_135_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_135_, 0, v_k_128_);
v___x_136_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_125_, v_bi_126_, v_type_127_, v___f_135_, v_kind_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_136_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_a_145_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_136_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_136_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___boxed(lean_object* v_name_153_, lean_object* v_bi_154_, lean_object* v_type_155_, lean_object* v_k_156_, lean_object* v_kind_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
uint8_t v_bi_boxed_163_; uint8_t v_kind_boxed_164_; lean_object* v_res_165_; 
v_bi_boxed_163_ = lean_unbox(v_bi_154_);
v_kind_boxed_164_ = lean_unbox(v_kind_157_);
v_res_165_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_name_153_, v_bi_boxed_163_, v_type_155_, v_k_156_, v_kind_boxed_164_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0(lean_object* v_00_u03b1_166_, lean_object* v_name_167_, uint8_t v_bi_168_, lean_object* v_type_169_, lean_object* v_k_170_, uint8_t v_kind_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_name_167_, v_bi_168_, v_type_169_, v_k_170_, v_kind_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___boxed(lean_object* v_00_u03b1_178_, lean_object* v_name_179_, lean_object* v_bi_180_, lean_object* v_type_181_, lean_object* v_k_182_, lean_object* v_kind_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
uint8_t v_bi_boxed_189_; uint8_t v_kind_boxed_190_; lean_object* v_res_191_; 
v_bi_boxed_189_ = lean_unbox(v_bi_180_);
v_kind_boxed_190_ = lean_unbox(v_kind_183_);
v_res_191_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0(v_00_u03b1_178_, v_name_179_, v_bi_boxed_189_, v_type_181_, v_k_182_, v_kind_boxed_190_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed(lean_object* v_xs_194_, lean_object* v_body_195_, lean_object* v_x_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(v_xs_194_, v_body_195_, v_x_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(lean_object* v_type_203_, lean_object* v_xs_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; 
switch(lean_obj_tag(v_type_203_))
{
case 3:
{
lean_object* v_u_237_; 
v_u_237_ = lean_ctor_get(v_type_203_, 0);
if (lean_obj_tag(v_u_237_) == 0)
{
lean_dec_ref(v_type_203_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_xs_204_);
goto v___jp_210_;
}
else
{
v___y_219_ = v_a_205_;
v___y_220_ = v_a_206_;
v___y_221_ = v_a_207_;
v___y_222_ = v_a_208_;
goto v___jp_218_;
}
}
case 7:
{
lean_object* v_binderName_238_; lean_object* v_binderType_239_; lean_object* v_body_240_; uint8_t v_binderInfo_241_; lean_object* v___f_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; 
v_binderName_238_ = lean_ctor_get(v_type_203_, 0);
lean_inc(v_binderName_238_);
v_binderType_239_ = lean_ctor_get(v_type_203_, 1);
lean_inc_ref(v_binderType_239_);
v_body_240_ = lean_ctor_get(v_type_203_, 2);
lean_inc_ref(v_body_240_);
v_binderInfo_241_ = lean_ctor_get_uint8(v_type_203_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_203_);
lean_inc_ref(v_xs_204_);
v___f_242_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_242_, 0, v_xs_204_);
lean_closure_set(v___f_242_, 1, v_body_240_);
v___x_243_ = lean_expr_instantiate_rev(v_binderType_239_, v_xs_204_);
lean_dec_ref(v_xs_204_);
lean_dec_ref(v_binderType_239_);
v___x_244_ = 0;
v___x_245_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_238_, v_binderInfo_241_, v___x_243_, v___f_242_, v___x_244_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
return v___x_245_;
}
default: 
{
v___y_219_ = v_a_205_;
v___y_220_ = v_a_206_;
v___y_221_ = v_a_207_;
v___y_222_ = v_a_208_;
goto v___jp_218_;
}
}
v___jp_210_:
{
uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = 1;
v___x_212_ = lean_box(v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
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
v___x_223_ = lean_expr_instantiate_rev(v_type_203_, v_xs_204_);
lean_dec_ref(v_xs_204_);
lean_dec_ref(v_type_203_);
lean_inc(v___y_222_);
lean_inc_ref(v___y_221_);
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
v___x_224_ = l_Lean_Meta_whnfD(v___x_223_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref(v___x_224_);
switch(lean_obj_tag(v_a_225_))
{
case 3:
{
lean_object* v_u_226_; 
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
v_u_226_ = lean_ctor_get(v_a_225_, 0);
lean_inc(v_u_226_);
lean_dec_ref(v_a_225_);
if (lean_obj_tag(v_u_226_) == 0)
{
goto v___jp_210_;
}
else
{
lean_dec(v_u_226_);
goto v___jp_214_;
}
}
case 7:
{
lean_object* v___x_227_; 
v___x_227_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v_type_203_ = v_a_225_;
v_xs_204_ = v___x_227_;
v_a_205_ = v___y_219_;
v_a_206_ = v___y_220_;
v_a_207_ = v___y_221_;
v_a_208_ = v___y_222_;
goto _start;
}
default: 
{
lean_dec(v_a_225_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
goto v___jp_214_;
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
v_a_229_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_224_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_224_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(lean_object* v_xs_246_, lean_object* v_body_247_, lean_object* v_x_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_array_push(v_xs_246_, v_x_248_);
v___x_255_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_body_247_, v___x_254_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___boxed(lean_object* v_type_256_, lean_object* v_xs_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_256_, v_xs_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType(lean_object* v_type_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
uint8_t v___x_270_; 
v___x_270_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_type_264_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_272_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_264_, v___x_271_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec_ref(v_type_264_);
v___x_273_ = lean_box(v___x_270_);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType___boxed(lean_object* v_type_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Compiler_LCNF_isPropFormerType(v_type_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer(lean_object* v_e_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_288_; 
lean_inc(v_a_286_);
lean_inc_ref(v_a_285_);
lean_inc(v_a_284_);
lean_inc_ref(v_a_283_);
v___x_288_ = lean_infer_type(v_e_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_290_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref(v___x_288_);
v___x_290_ = l_Lean_Compiler_LCNF_isPropFormerType(v_a_289_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
return v___x_290_;
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
v_a_291_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_288_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_288_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer___boxed(lean_object* v_e_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Compiler_LCNF_isPropFormer(v_e_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
return v_res_305_;
}
}
static uint64_t _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0(void){
_start:
{
uint8_t v___x_306_; uint64_t v___x_307_; 
v___x_306_ = 0;
v___x_307_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(lean_object* v_type_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; uint8_t v_foApprox_315_; uint8_t v_ctxApprox_316_; uint8_t v_quasiPatternApprox_317_; uint8_t v_constApprox_318_; uint8_t v_isDefEqStuckEx_319_; uint8_t v_unificationHints_320_; uint8_t v_proofIrrelevance_321_; uint8_t v_assignSyntheticOpaque_322_; uint8_t v_offsetCnstrs_323_; uint8_t v_etaStruct_324_; uint8_t v_univApprox_325_; uint8_t v_iota_326_; uint8_t v_beta_327_; uint8_t v_proj_328_; uint8_t v_zeta_329_; uint8_t v_zetaDelta_330_; uint8_t v_zetaUnused_331_; uint8_t v_zetaHave_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_363_; 
v___x_314_ = l_Lean_Meta_Context_config(v_a_309_);
v_foApprox_315_ = lean_ctor_get_uint8(v___x_314_, 0);
v_ctxApprox_316_ = lean_ctor_get_uint8(v___x_314_, 1);
v_quasiPatternApprox_317_ = lean_ctor_get_uint8(v___x_314_, 2);
v_constApprox_318_ = lean_ctor_get_uint8(v___x_314_, 3);
v_isDefEqStuckEx_319_ = lean_ctor_get_uint8(v___x_314_, 4);
v_unificationHints_320_ = lean_ctor_get_uint8(v___x_314_, 5);
v_proofIrrelevance_321_ = lean_ctor_get_uint8(v___x_314_, 6);
v_assignSyntheticOpaque_322_ = lean_ctor_get_uint8(v___x_314_, 7);
v_offsetCnstrs_323_ = lean_ctor_get_uint8(v___x_314_, 8);
v_etaStruct_324_ = lean_ctor_get_uint8(v___x_314_, 10);
v_univApprox_325_ = lean_ctor_get_uint8(v___x_314_, 11);
v_iota_326_ = lean_ctor_get_uint8(v___x_314_, 12);
v_beta_327_ = lean_ctor_get_uint8(v___x_314_, 13);
v_proj_328_ = lean_ctor_get_uint8(v___x_314_, 14);
v_zeta_329_ = lean_ctor_get_uint8(v___x_314_, 15);
v_zetaDelta_330_ = lean_ctor_get_uint8(v___x_314_, 16);
v_zetaUnused_331_ = lean_ctor_get_uint8(v___x_314_, 17);
v_zetaHave_332_ = lean_ctor_get_uint8(v___x_314_, 18);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_363_ == 0)
{
v___x_334_ = v___x_314_;
v_isShared_335_ = v_isSharedCheck_363_;
goto v_resetjp_333_;
}
else
{
lean_dec(v___x_314_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_363_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
uint8_t v_trackZetaDelta_336_; lean_object* v_zetaDeltaSet_337_; lean_object* v_lctx_338_; lean_object* v_localInstances_339_; lean_object* v_defEqCtx_x3f_340_; lean_object* v_synthPendingDepth_341_; lean_object* v_canUnfold_x3f_342_; uint8_t v_univApprox_343_; uint8_t v_inTypeClassResolution_344_; uint8_t v_cacheInferType_345_; uint8_t v___x_346_; lean_object* v_config_348_; 
v_trackZetaDelta_336_ = lean_ctor_get_uint8(v_a_309_, sizeof(void*)*7);
v_zetaDeltaSet_337_ = lean_ctor_get(v_a_309_, 1);
v_lctx_338_ = lean_ctor_get(v_a_309_, 2);
v_localInstances_339_ = lean_ctor_get(v_a_309_, 3);
v_defEqCtx_x3f_340_ = lean_ctor_get(v_a_309_, 4);
v_synthPendingDepth_341_ = lean_ctor_get(v_a_309_, 5);
v_canUnfold_x3f_342_ = lean_ctor_get(v_a_309_, 6);
v_univApprox_343_ = lean_ctor_get_uint8(v_a_309_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_344_ = lean_ctor_get_uint8(v_a_309_, sizeof(void*)*7 + 2);
v_cacheInferType_345_ = lean_ctor_get_uint8(v_a_309_, sizeof(void*)*7 + 3);
v___x_346_ = 0;
if (v_isShared_335_ == 0)
{
v_config_348_ = v___x_334_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 0, v_foApprox_315_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 1, v_ctxApprox_316_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 2, v_quasiPatternApprox_317_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 3, v_constApprox_318_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 4, v_isDefEqStuckEx_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 5, v_unificationHints_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 6, v_proofIrrelevance_321_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 7, v_assignSyntheticOpaque_322_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 8, v_offsetCnstrs_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 10, v_etaStruct_324_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 11, v_univApprox_325_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 12, v_iota_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 13, v_beta_327_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 14, v_proj_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 15, v_zeta_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 16, v_zetaDelta_330_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 17, v_zetaUnused_331_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 18, v_zetaHave_332_);
v_config_348_ = v_reuseFailAlloc_362_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
uint64_t v___x_349_; uint64_t v___x_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v_key_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_ctor_set_uint8(v_config_348_, 9, v___x_346_);
v___x_349_ = l_Lean_Meta_Context_configKey(v_a_309_);
v___x_350_ = 2ULL;
v___x_351_ = lean_uint64_shift_right(v___x_349_, v___x_350_);
v___x_352_ = lean_uint64_shift_left(v___x_351_, v___x_350_);
v___x_353_ = lean_uint64_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0);
v_key_354_ = lean_uint64_lor(v___x_352_, v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_355_, 0, v_config_348_);
lean_ctor_set_uint64(v___x_355_, sizeof(void*)*1, v_key_354_);
lean_inc(v_canUnfold_x3f_342_);
lean_inc(v_synthPendingDepth_341_);
lean_inc(v_defEqCtx_x3f_340_);
lean_inc_ref(v_localInstances_339_);
lean_inc_ref(v_lctx_338_);
lean_inc(v_zetaDeltaSet_337_);
v___x_356_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_zetaDeltaSet_337_);
lean_ctor_set(v___x_356_, 2, v_lctx_338_);
lean_ctor_set(v___x_356_, 3, v_localInstances_339_);
lean_ctor_set(v___x_356_, 4, v_defEqCtx_x3f_340_);
lean_ctor_set(v___x_356_, 5, v_synthPendingDepth_341_);
lean_ctor_set(v___x_356_, 6, v_canUnfold_x3f_342_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*7, v_trackZetaDelta_336_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*7 + 1, v_univApprox_343_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*7 + 2, v_inTypeClassResolution_344_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*7 + 3, v_cacheInferType_345_);
lean_inc(v_a_312_);
lean_inc_ref(v_a_311_);
lean_inc(v_a_310_);
v___x_357_ = lean_whnf(v_type_308_, v___x_356_, v_a_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_inc(v_a_358_);
v___x_359_ = l_Lean_Expr_eta(v_a_358_);
v___x_360_ = lean_expr_eqv(v___x_359_, v_a_358_);
lean_dec(v_a_358_);
if (v___x_360_ == 0)
{
lean_dec_ref(v___x_357_);
v_type_308_ = v___x_359_;
goto _start;
}
else
{
lean_dec_ref(v___x_359_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
return v___x_357_;
}
}
else
{
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
return v___x_357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___boxed(lean_object* v_type_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec_ref(v_a_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(lean_object* v_msgData_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; lean_object* v_env_378_; lean_object* v___x_379_; lean_object* v_mctx_380_; lean_object* v_lctx_381_; lean_object* v_options_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_377_ = lean_st_ref_get(v___y_375_);
v_env_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_env_378_);
lean_dec(v___x_377_);
v___x_379_ = lean_st_ref_get(v___y_373_);
v_mctx_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc_ref(v_mctx_380_);
lean_dec(v___x_379_);
v_lctx_381_ = lean_ctor_get(v___y_372_, 2);
v_options_382_ = lean_ctor_get(v___y_374_, 2);
lean_inc_ref(v_options_382_);
lean_inc_ref(v_lctx_381_);
v___x_383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_383_, 0, v_env_378_);
lean_ctor_set(v___x_383_, 1, v_mctx_380_);
lean_ctor_set(v___x_383_, 2, v_lctx_381_);
lean_ctor_set(v___x_383_, 3, v_options_382_);
v___x_384_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_msgData_371_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6___boxed(lean_object* v_msgData_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msgData_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(lean_object* v_msg_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_ref_399_; lean_object* v___x_400_; lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_ref_399_ = lean_ctor_get(v___y_396_, 5);
v___x_400_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msg_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
lean_inc(v_ref_399_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_ref_399_);
lean_ctor_set(v___x_405_, 1, v_a_401_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 1);
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg___boxed(lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(lean_object* v_ref_417_, lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_fileName_424_; lean_object* v_fileMap_425_; lean_object* v_options_426_; lean_object* v_currRecDepth_427_; lean_object* v_maxRecDepth_428_; lean_object* v_ref_429_; lean_object* v_currNamespace_430_; lean_object* v_openDecls_431_; lean_object* v_initHeartbeats_432_; lean_object* v_maxHeartbeats_433_; lean_object* v_quotContext_434_; lean_object* v_currMacroScope_435_; uint8_t v_diag_436_; lean_object* v_cancelTk_x3f_437_; uint8_t v_suppressElabErrors_438_; lean_object* v_inheritedTraceOptions_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_448_; 
v_fileName_424_ = lean_ctor_get(v___y_421_, 0);
v_fileMap_425_ = lean_ctor_get(v___y_421_, 1);
v_options_426_ = lean_ctor_get(v___y_421_, 2);
v_currRecDepth_427_ = lean_ctor_get(v___y_421_, 3);
v_maxRecDepth_428_ = lean_ctor_get(v___y_421_, 4);
v_ref_429_ = lean_ctor_get(v___y_421_, 5);
v_currNamespace_430_ = lean_ctor_get(v___y_421_, 6);
v_openDecls_431_ = lean_ctor_get(v___y_421_, 7);
v_initHeartbeats_432_ = lean_ctor_get(v___y_421_, 8);
v_maxHeartbeats_433_ = lean_ctor_get(v___y_421_, 9);
v_quotContext_434_ = lean_ctor_get(v___y_421_, 10);
v_currMacroScope_435_ = lean_ctor_get(v___y_421_, 11);
v_diag_436_ = lean_ctor_get_uint8(v___y_421_, sizeof(void*)*14);
v_cancelTk_x3f_437_ = lean_ctor_get(v___y_421_, 12);
v_suppressElabErrors_438_ = lean_ctor_get_uint8(v___y_421_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_439_ = lean_ctor_get(v___y_421_, 13);
v_isSharedCheck_448_ = !lean_is_exclusive(v___y_421_);
if (v_isSharedCheck_448_ == 0)
{
v___x_441_ = v___y_421_;
v_isShared_442_ = v_isSharedCheck_448_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_inheritedTraceOptions_439_);
lean_inc(v_cancelTk_x3f_437_);
lean_inc(v_currMacroScope_435_);
lean_inc(v_quotContext_434_);
lean_inc(v_maxHeartbeats_433_);
lean_inc(v_initHeartbeats_432_);
lean_inc(v_openDecls_431_);
lean_inc(v_currNamespace_430_);
lean_inc(v_ref_429_);
lean_inc(v_maxRecDepth_428_);
lean_inc(v_currRecDepth_427_);
lean_inc(v_options_426_);
lean_inc(v_fileMap_425_);
lean_inc(v_fileName_424_);
lean_dec(v___y_421_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_448_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_ref_443_; lean_object* v___x_445_; 
v_ref_443_ = l_Lean_replaceRef(v_ref_417_, v_ref_429_);
lean_dec(v_ref_429_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 5, v_ref_443_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_fileName_424_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_fileMap_425_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_options_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_currRecDepth_427_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_maxRecDepth_428_);
lean_ctor_set(v_reuseFailAlloc_447_, 5, v_ref_443_);
lean_ctor_set(v_reuseFailAlloc_447_, 6, v_currNamespace_430_);
lean_ctor_set(v_reuseFailAlloc_447_, 7, v_openDecls_431_);
lean_ctor_set(v_reuseFailAlloc_447_, 8, v_initHeartbeats_432_);
lean_ctor_set(v_reuseFailAlloc_447_, 9, v_maxHeartbeats_433_);
lean_ctor_set(v_reuseFailAlloc_447_, 10, v_quotContext_434_);
lean_ctor_set(v_reuseFailAlloc_447_, 11, v_currMacroScope_435_);
lean_ctor_set(v_reuseFailAlloc_447_, 12, v_cancelTk_x3f_437_);
lean_ctor_set(v_reuseFailAlloc_447_, 13, v_inheritedTraceOptions_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*14, v_diag_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*14 + 1, v_suppressElabErrors_438_);
v___x_445_ = v_reuseFailAlloc_447_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_418_, v___y_419_, v___y_420_, v___x_445_, v___y_422_);
lean_dec_ref(v___x_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg___boxed(lean_object* v_ref_449_, lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_449_, v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v_ref_449_);
return v_res_456_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
lean_ctor_set(v___x_462_, 2, v___x_461_);
lean_ctor_set(v___x_462_, 3, v___x_460_);
lean_ctor_set(v___x_462_, 4, v___x_460_);
lean_ctor_set(v___x_462_, 5, v___x_460_);
lean_ctor_set(v___x_462_, 6, v___x_460_);
lean_ctor_set(v___x_462_, 7, v___x_460_);
lean_ctor_set(v___x_462_, 8, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_unsigned_to_nat(32u);
v___x_464_ = lean_mk_empty_array_with_capacity(v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_466_ = ((size_t)5ULL);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_unsigned_to_nat(32u);
v___x_469_ = lean_mk_empty_array_with_capacity(v___x_468_);
v___x_470_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_471_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
lean_ctor_set(v___x_471_, 2, v___x_467_);
lean_ctor_set(v___x_471_, 3, v___x_467_);
lean_ctor_set_usize(v___x_471_, 4, v___x_466_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_472_ = lean_box(1);
v___x_473_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_474_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v___x_473_);
lean_ctor_set(v___x_475_, 2, v___x_472_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_481_ = l_Lean_stringToMessageData(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_487_ = l_Lean_stringToMessageData(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_497_, lean_object* v_declHint_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; lean_object* v_env_502_; uint8_t v___x_503_; 
v___x_501_ = lean_st_ref_get(v___y_499_);
v_env_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc_ref(v_env_502_);
lean_dec(v___x_501_);
v___x_503_ = l_Lean_Name_isAnonymous(v_declHint_498_);
if (v___x_503_ == 0)
{
uint8_t v_isExporting_504_; 
v_isExporting_504_ = lean_ctor_get_uint8(v_env_502_, sizeof(void*)*8);
if (v_isExporting_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec_ref(v_env_502_);
lean_dec(v_declHint_498_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v_msg_497_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; uint8_t v___x_507_; 
lean_inc_ref(v_env_502_);
v___x_506_ = l_Lean_Environment_setExporting(v_env_502_, v___x_503_);
lean_inc(v_declHint_498_);
lean_inc_ref(v___x_506_);
v___x_507_ = l_Lean_Environment_contains(v___x_506_, v_declHint_498_, v_isExporting_504_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec_ref(v___x_506_);
lean_dec_ref(v_env_502_);
lean_dec(v_declHint_498_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v_msg_497_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_c_514_; lean_object* v___x_515_; 
v___x_509_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_510_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_511_ = l_Lean_Options_empty;
v___x_512_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_512_, 0, v___x_506_);
lean_ctor_set(v___x_512_, 1, v___x_509_);
lean_ctor_set(v___x_512_, 2, v___x_510_);
lean_ctor_set(v___x_512_, 3, v___x_511_);
lean_inc(v_declHint_498_);
v___x_513_ = l_Lean_MessageData_ofConstName(v_declHint_498_, v___x_503_);
v_c_514_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_514_, 0, v___x_512_);
lean_ctor_set(v_c_514_, 1, v___x_513_);
v___x_515_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_502_, v_declHint_498_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec_ref(v_env_502_);
lean_dec(v_declHint_498_);
v___x_516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v_c_514_);
v___x_518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = l_Lean_MessageData_note(v___x_519_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v_msg_497_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
else
{
lean_object* v_val_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_558_; 
v_val_523_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_558_ == 0)
{
v___x_525_ = v___x_515_;
v_isShared_526_ = v_isSharedCheck_558_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_val_523_);
lean_dec(v___x_515_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_558_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_mod_530_; uint8_t v___x_531_; 
v___x_527_ = lean_box(0);
v___x_528_ = l_Lean_Environment_header(v_env_502_);
lean_dec_ref(v_env_502_);
v___x_529_ = l_Lean_EnvironmentHeader_moduleNames(v___x_528_);
v_mod_530_ = lean_array_get(v___x_527_, v___x_529_, v_val_523_);
lean_dec(v_val_523_);
lean_dec_ref(v___x_529_);
v___x_531_ = l_Lean_isPrivateName(v_declHint_498_);
lean_dec(v_declHint_498_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_c_514_);
v___x_534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Lean_MessageData_ofName(v_mod_530_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l_Lean_MessageData_note(v___x_539_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v_msg_497_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 0);
lean_ctor_set(v___x_525_, 0, v___x_541_);
v___x_543_ = v___x_525_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v_c_514_);
v___x_547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = l_Lean_MessageData_ofName(v_mod_530_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Lean_MessageData_note(v___x_552_);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v_msg_497_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 0);
lean_ctor_set(v___x_525_, 0, v___x_554_);
v___x_556_ = v___x_525_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_559_; 
lean_dec_ref(v_env_502_);
lean_dec(v_declHint_498_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v_msg_497_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_560_, lean_object* v_declHint_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_560_, v_declHint_561_, v___y_562_);
lean_dec(v___y_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(lean_object* v_msg_565_, lean_object* v_declHint_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_582_; 
v___x_572_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_565_, v_declHint_566_, v___y_570_);
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_582_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = l_Lean_unknownIdentifierMessageTag;
v___x_578_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v_a_573_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_578_);
v___x_580_ = v___x_575_;
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
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9___boxed(lean_object* v_msg_583_, lean_object* v_declHint_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_583_, v_declHint_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(lean_object* v_ref_591_, lean_object* v_msg_592_, lean_object* v_declHint_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; lean_object* v_a_600_; lean_object* v___x_601_; 
v___x_599_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_592_, v_declHint_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref(v___x_599_);
v___x_601_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_591_, v_a_600_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_ref_602_, lean_object* v_msg_603_, lean_object* v_declHint_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_602_, v_msg_603_, v_declHint_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v_ref_602_);
return v_res_610_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0));
v___x_613_ = l_Lean_stringToMessageData(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2));
v___x_616_ = l_Lean_stringToMessageData(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(lean_object* v_ref_617_, lean_object* v_constName_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_624_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1);
v___x_625_ = 0;
lean_inc(v_constName_618_);
v___x_626_ = l_Lean_MessageData_ofConstName(v_constName_618_, v___x_625_);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_624_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3);
v___x_629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_617_, v___x_629_, v_constName_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___boxed(lean_object* v_ref_631_, lean_object* v_constName_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_631_, v_constName_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v_ref_631_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(lean_object* v_constName_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_ref_645_; lean_object* v___x_646_; 
v_ref_645_ = lean_ctor_get(v___y_642_, 5);
lean_inc(v_ref_645_);
v___x_646_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_645_, v_constName_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v_ref_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg___boxed(lean_object* v_constName_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(lean_object* v_constName_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; lean_object* v_env_661_; uint8_t v___x_662_; lean_object* v___x_663_; 
v___x_660_ = lean_st_ref_get(v___y_658_);
v_env_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc_ref(v_env_661_);
lean_dec(v___x_660_);
v___x_662_ = 0;
lean_inc(v_constName_654_);
v___x_663_ = l_Lean_Environment_find_x3f(v_env_661_, v_constName_654_, v___x_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v___x_664_;
}
else
{
lean_object* v_val_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v___y_657_);
lean_dec(v_constName_654_);
v_val_665_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_663_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_val_665_);
lean_dec(v___x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set_tag(v___x_667_, 0);
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_val_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4___boxed(lean_object* v_constName_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_constName_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(lean_object* v_binderType_680_, lean_object* v_body_681_, lean_object* v_binderName_682_, uint8_t v_binderInfo_683_, lean_object* v_x_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; 
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_686_);
lean_inc_ref(v___y_685_);
v___x_690_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_binderType_680_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref(v___x_690_);
v___x_692_ = lean_expr_instantiate1(v_body_681_, v_x_684_);
v___x_693_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_692_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; uint8_t v___x_695_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
v___x_695_ = l_Lean_Expr_isErased(v_a_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_707_; 
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v___x_693_, 0);
lean_dec(v_unused_708_);
v___x_697_ = v___x_693_;
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
else
{
lean_dec(v___x_693_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_mk_empty_array_with_capacity(v___x_699_);
v___x_701_ = lean_array_push(v___x_700_, v_x_684_);
v___x_702_ = lean_expr_abstract(v_a_694_, v___x_701_);
lean_dec_ref(v___x_701_);
lean_dec(v_a_694_);
v___x_703_ = l_Lean_Expr_lam___override(v_binderName_682_, v_a_691_, v___x_702_, v_binderInfo_683_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_703_);
v___x_705_ = v___x_697_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_dec(v_a_694_);
lean_dec(v_a_691_);
lean_dec_ref(v_x_684_);
lean_dec(v_binderName_682_);
return v___x_693_;
}
}
else
{
lean_dec(v_a_691_);
lean_dec_ref(v_x_684_);
lean_dec(v_binderName_682_);
return v___x_693_;
}
}
else
{
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v_x_684_);
lean_dec(v_binderName_682_);
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed(lean_object* v_binderType_709_, lean_object* v_body_710_, lean_object* v_binderName_711_, lean_object* v_binderInfo_712_, lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v_binderInfo_10213__boxed_719_; lean_object* v_res_720_; 
v_binderInfo_10213__boxed_719_ = lean_unbox(v_binderInfo_712_);
v_res_720_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(v_binderType_709_, v_body_710_, v_binderName_711_, v_binderInfo_10213__boxed_719_, v_x_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec_ref(v_body_710_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(lean_object* v_d_721_, lean_object* v_xs_722_, lean_object* v_body_723_, lean_object* v_binderName_724_, uint8_t v_binderInfo_725_, lean_object* v_x_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
uint8_t v_isBorrowed_732_; lean_object* v___x_733_; 
v_isBorrowed_732_ = l_Lean_isMarkedBorrowed(v_d_721_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
v___x_733_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_d_721_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v_d_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___x_752_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref(v___x_733_);
v___x_752_ = lean_expr_abstract(v_a_734_, v_xs_722_);
lean_dec(v_a_734_);
if (v_isBorrowed_732_ == 0)
{
v_d_736_ = v___x_752_;
v___y_737_ = v___y_727_;
v___y_738_ = v___y_728_;
v___y_739_ = v___y_729_;
v___y_740_ = v___y_730_;
goto v___jp_735_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_markBorrowed(v___x_752_);
v_d_736_ = v___x_753_;
v___y_737_ = v___y_727_;
v___y_738_ = v___y_728_;
v___y_739_ = v___y_729_;
v___y_740_ = v___y_730_;
goto v___jp_735_;
}
v___jp_735_:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_array_push(v_xs_722_, v_x_726_);
v___x_742_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_body_723_, v___x_741_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_751_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_751_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = l_Lean_Expr_forallE___override(v_binderName_724_, v_d_736_, v_a_743_, v_binderInfo_725_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_dec_ref(v_d_736_);
lean_dec(v_binderName_724_);
return v___x_742_;
}
}
}
else
{
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec_ref(v_x_726_);
lean_dec(v_binderName_724_);
lean_dec_ref(v_body_723_);
lean_dec_ref(v_xs_722_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed(lean_object* v_d_754_, lean_object* v_xs_755_, lean_object* v_body_756_, lean_object* v_binderName_757_, lean_object* v_binderInfo_758_, lean_object* v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
uint8_t v_binderInfo_10235__boxed_765_; lean_object* v_res_766_; 
v_binderInfo_10235__boxed_765_ = lean_unbox(v_binderInfo_758_);
v_res_766_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(v_d_754_, v_xs_755_, v_body_756_, v_binderName_757_, v_binderInfo_10235__boxed_765_, v_x_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(lean_object* v_e_767_, lean_object* v_xs_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
if (lean_obj_tag(v_e_767_) == 7)
{
lean_object* v_binderName_774_; lean_object* v_binderType_775_; lean_object* v_body_776_; uint8_t v_binderInfo_777_; lean_object* v_d_778_; lean_object* v___x_779_; lean_object* v___f_780_; uint8_t v___x_781_; lean_object* v___x_782_; 
v_binderName_774_ = lean_ctor_get(v_e_767_, 0);
lean_inc(v_binderName_774_);
v_binderType_775_ = lean_ctor_get(v_e_767_, 1);
lean_inc_ref(v_binderType_775_);
v_body_776_ = lean_ctor_get(v_e_767_, 2);
lean_inc_ref(v_body_776_);
v_binderInfo_777_ = lean_ctor_get_uint8(v_e_767_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_767_);
v_d_778_ = lean_expr_instantiate_rev(v_binderType_775_, v_xs_768_);
lean_dec_ref(v_binderType_775_);
v___x_779_ = lean_box(v_binderInfo_777_);
lean_inc(v_binderName_774_);
lean_inc_ref(v_d_778_);
v___f_780_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed), 11, 5);
lean_closure_set(v___f_780_, 0, v_d_778_);
lean_closure_set(v___f_780_, 1, v_xs_768_);
lean_closure_set(v___f_780_, 2, v_body_776_);
lean_closure_set(v___f_780_, 3, v_binderName_774_);
lean_closure_set(v___f_780_, 4, v___x_779_);
v___x_781_ = 0;
v___x_782_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_774_, v_binderInfo_777_, v_d_778_, v___f_780_, v___x_781_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
return v___x_782_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_expr_instantiate_rev(v_e_767_, v_xs_768_);
lean_dec_ref(v_e_767_);
v___x_784_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_783_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_793_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_793_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_expr_abstract(v_a_785_, v_xs_768_);
lean_dec_ref(v_xs_768_);
lean_dec(v_a_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
lean_dec_ref(v_xs_768_);
return v___x_784_;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0(void){
_start:
{
lean_object* v___x_794_; lean_object* v_dummy_795_; 
v___x_794_ = lean_box(0);
v_dummy_795_ = l_Lean_Expr_sort___override(v___x_794_);
return v_dummy_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(lean_object* v_type_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_805_; 
lean_inc(v_a_803_);
lean_inc_ref(v_a_802_);
lean_inc(v_a_801_);
lean_inc_ref(v_a_800_);
lean_inc_ref(v_type_799_);
v___x_805_ = l_Lean_Meta_isProp(v_type_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_872_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_872_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_872_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_872_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
uint8_t v___x_810_; 
v___x_810_ = lean_unbox(v_a_806_);
lean_dec(v_a_806_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
lean_inc(v_a_803_);
lean_inc_ref(v_a_802_);
lean_inc(v_a_801_);
v___x_811_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
switch(lean_obj_tag(v_a_812_))
{
case 3:
{
lean_dec_ref(v_a_812_);
lean_del_object(v___x_808_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v___x_811_;
}
case 4:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v___x_811_);
lean_del_object(v___x_808_);
v___x_818_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_819_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_812_, v___x_818_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
return v___x_819_;
}
case 6:
{
lean_object* v_binderName_820_; lean_object* v_binderType_821_; lean_object* v_body_822_; uint8_t v_binderInfo_823_; lean_object* v___x_824_; lean_object* v___f_825_; uint8_t v___x_826_; lean_object* v___x_827_; 
lean_dec_ref(v___x_811_);
lean_del_object(v___x_808_);
v_binderName_820_ = lean_ctor_get(v_a_812_, 0);
lean_inc(v_binderName_820_);
v_binderType_821_ = lean_ctor_get(v_a_812_, 1);
lean_inc_ref(v_binderType_821_);
v_body_822_ = lean_ctor_get(v_a_812_, 2);
lean_inc_ref(v_body_822_);
v_binderInfo_823_ = lean_ctor_get_uint8(v_a_812_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_812_);
v___x_824_ = lean_box(v_binderInfo_823_);
lean_inc(v_binderName_820_);
lean_inc_ref(v_binderType_821_);
v___f_825_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_825_, 0, v_binderType_821_);
lean_closure_set(v___f_825_, 1, v_body_822_);
lean_closure_set(v___f_825_, 2, v_binderName_820_);
lean_closure_set(v___f_825_, 3, v___x_824_);
v___x_826_ = 0;
v___x_827_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_820_, v_binderInfo_823_, v_binderType_821_, v___f_825_, v___x_826_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
return v___x_827_;
}
case 7:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec_ref(v___x_811_);
lean_del_object(v___x_808_);
v___x_828_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_829_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_a_812_, v___x_828_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
return v___x_829_;
}
case 5:
{
lean_object* v_dummy_830_; lean_object* v_nargs_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v___x_811_);
lean_del_object(v___x_808_);
v_dummy_830_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0);
v_nargs_831_ = l_Lean_Expr_getAppNumArgs(v_a_812_);
lean_inc(v_nargs_831_);
v___x_832_ = lean_mk_array(v_nargs_831_, v_dummy_830_);
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_sub(v_nargs_831_, v___x_833_);
lean_dec(v_nargs_831_);
v___x_835_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_a_812_, v___x_832_, v___x_834_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
return v___x_835_;
}
case 1:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v___x_811_);
lean_del_object(v___x_808_);
v___x_836_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_837_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_812_, v___x_836_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
return v___x_837_;
}
case 11:
{
lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_866_; 
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v___x_811_, 0);
lean_dec(v_unused_867_);
v___x_839_ = v___x_811_;
v_isShared_840_ = v_isSharedCheck_866_;
goto v_resetjp_838_;
}
else
{
lean_dec(v___x_811_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_866_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_typeName_841_; 
v_typeName_841_ = lean_ctor_get(v_a_812_, 0);
lean_inc(v_typeName_841_);
if (lean_obj_tag(v_typeName_841_) == 1)
{
lean_object* v_pre_842_; 
v_pre_842_ = lean_ctor_get(v_typeName_841_, 0);
if (lean_obj_tag(v_pre_842_) == 0)
{
lean_object* v_idx_843_; lean_object* v_struct_844_; lean_object* v_str_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_idx_843_ = lean_ctor_get(v_a_812_, 1);
lean_inc(v_idx_843_);
v_struct_844_ = lean_ctor_get(v_a_812_, 2);
lean_inc_ref(v_struct_844_);
lean_dec_ref(v_a_812_);
v_str_845_ = lean_ctor_get(v_typeName_841_, 1);
lean_inc_ref(v_str_845_);
lean_dec_ref(v_typeName_841_);
v___x_846_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1));
v___x_847_ = lean_string_dec_eq(v_str_845_, v___x_846_);
lean_dec_ref(v_str_845_);
if (v___x_847_ == 0)
{
lean_dec_ref(v_struct_844_);
lean_dec(v_idx_843_);
lean_del_object(v___x_839_);
goto v___jp_813_;
}
else
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_nat_dec_eq(v_idx_843_, v___x_848_);
lean_dec(v_idx_843_);
if (v___x_849_ == 0)
{
lean_dec_ref(v_struct_844_);
lean_del_object(v___x_839_);
goto v___jp_813_;
}
else
{
if (lean_obj_tag(v_struct_844_) == 5)
{
lean_object* v_fn_850_; 
v_fn_850_ = lean_ctor_get(v_struct_844_, 0);
lean_inc_ref(v_fn_850_);
lean_dec_ref(v_struct_844_);
if (lean_obj_tag(v_fn_850_) == 4)
{
lean_object* v_declName_851_; 
v_declName_851_ = lean_ctor_get(v_fn_850_, 0);
lean_inc(v_declName_851_);
if (lean_obj_tag(v_declName_851_) == 1)
{
lean_object* v_pre_852_; 
v_pre_852_ = lean_ctor_get(v_declName_851_, 0);
lean_inc(v_pre_852_);
if (lean_obj_tag(v_pre_852_) == 1)
{
lean_object* v_pre_853_; 
v_pre_853_ = lean_ctor_get(v_pre_852_, 0);
if (lean_obj_tag(v_pre_853_) == 0)
{
lean_object* v_us_854_; lean_object* v_str_855_; lean_object* v_str_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_us_854_ = lean_ctor_get(v_fn_850_, 1);
lean_inc(v_us_854_);
lean_dec_ref(v_fn_850_);
v_str_855_ = lean_ctor_get(v_declName_851_, 1);
lean_inc_ref(v_str_855_);
lean_dec_ref(v_declName_851_);
v_str_856_ = lean_ctor_get(v_pre_852_, 1);
lean_inc_ref(v_str_856_);
lean_dec_ref(v_pre_852_);
v___x_857_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2));
v___x_858_ = lean_string_dec_eq(v_str_856_, v___x_857_);
lean_dec_ref(v_str_856_);
if (v___x_858_ == 0)
{
lean_dec_ref(v_str_855_);
lean_dec(v_us_854_);
lean_del_object(v___x_839_);
goto v___jp_813_;
}
else
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3));
v___x_860_ = lean_string_dec_eq(v_str_855_, v___x_859_);
lean_dec_ref(v_str_855_);
if (v___x_860_ == 0)
{
lean_dec(v_us_854_);
lean_del_object(v___x_839_);
goto v___jp_813_;
}
else
{
if (lean_obj_tag(v_us_854_) == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
lean_del_object(v___x_808_);
v___x_861_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_862_ = l_Lean_mkConst(v___x_861_, v_us_854_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_862_);
v___x_864_ = v___x_839_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_dec(v_us_854_);
lean_del_object(v___x_839_);
goto v___jp_813_;
}
}
}
}
else
{
lean_dec_ref(v_pre_852_);
lean_dec_ref(v_declName_851_);
lean_dec_ref(v_fn_850_);
lean_del_object(v___x_839_);
goto v___jp_813_;
}
}
else
{
lean_dec_ref(v_declName_851_);
lean_dec(v_pre_852_);
lean_dec_ref(v_fn_850_);
lean_del_object(v___x_839_);
goto v___jp_813_;
}
}
else
{
lean_dec(v_declName_851_);
lean_dec_ref(v_fn_850_);
lean_del_object(v___x_839_);
goto v___jp_813_;
}
}
else
{
lean_dec_ref(v_fn_850_);
lean_del_object(v___x_839_);
goto v___jp_813_;
}
}
else
{
lean_dec_ref(v_struct_844_);
lean_del_object(v___x_839_);
goto v___jp_813_;
}
}
}
}
else
{
lean_dec_ref(v_typeName_841_);
lean_del_object(v___x_839_);
lean_dec_ref(v_a_812_);
goto v___jp_813_;
}
}
else
{
lean_dec(v_typeName_841_);
lean_del_object(v___x_839_);
lean_dec_ref(v_a_812_);
goto v___jp_813_;
}
}
}
default: 
{
lean_dec(v_a_812_);
lean_dec_ref(v___x_811_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
goto v___jp_813_;
}
}
v___jp_813_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_814_);
v___x_816_ = v___x_808_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
else
{
lean_del_object(v___x_808_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v___x_811_;
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_870_; 
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec_ref(v_type_799_);
v___x_868_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_868_);
v___x_870_ = v___x_808_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec_ref(v_type_799_);
v_a_873_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_805_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_805_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(lean_object* v_as_881_, size_t v_sz_882_, size_t v_i_883_, lean_object* v_b_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_a_891_; uint8_t v___x_895_; 
v___x_895_ = lean_usize_dec_lt(v_i_883_, v_sz_882_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v_b_884_);
return v___x_896_;
}
else
{
lean_object* v_a_897_; lean_object* v___y_899_; lean_object* v___x_928_; 
v_a_897_ = lean_array_uget_borrowed(v_as_881_, v_i_883_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v_a_897_);
v___x_928_ = l_Lean_Meta_isProp(v_a_897_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; uint8_t v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
v___x_930_ = lean_unbox(v_a_929_);
lean_dec(v_a_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec_ref(v___x_928_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v_a_897_);
v___x_931_ = l_Lean_Compiler_LCNF_isPropFormer(v_a_897_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
v___y_899_ = v___x_931_;
goto v___jp_898_;
}
else
{
v___y_899_ = v___x_928_;
goto v___jp_898_;
}
}
else
{
v___y_899_ = v___x_928_;
goto v___jp_898_;
}
v___jp_898_:
{
if (lean_obj_tag(v___y_899_) == 0)
{
lean_object* v_a_900_; uint8_t v___x_901_; 
v_a_900_ = lean_ctor_get(v___y_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v___y_899_);
v___x_901_ = lean_unbox(v_a_900_);
lean_dec(v_a_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v_a_897_);
v___x_902_ = l_Lean_Meta_isTypeFormer(v_a_897_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; uint8_t v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
v___x_904_ = lean_unbox(v_a_903_);
lean_dec(v_a_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_906_ = l_Lean_Expr_app___override(v_b_884_, v___x_905_);
v_a_891_ = v___x_906_;
goto v___jp_890_;
}
else
{
lean_object* v___x_907_; 
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v_a_897_);
v___x_907_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_a_897_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_907_);
v___x_909_ = l_Lean_Expr_app___override(v_b_884_, v_a_908_);
v_a_891_ = v___x_909_;
goto v___jp_890_;
}
else
{
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v_b_884_);
return v___x_907_;
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v_b_884_);
v_a_910_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_902_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_902_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_919_ = l_Lean_Expr_app___override(v_b_884_, v___x_918_);
v_a_891_ = v___x_919_;
goto v___jp_890_;
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v_b_884_);
v_a_920_ = lean_ctor_get(v___y_899_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___y_899_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___y_899_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___y_899_);
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
}
v___jp_890_:
{
size_t v___x_892_; size_t v___x_893_; 
v___x_892_ = ((size_t)1ULL);
v___x_893_ = lean_usize_add(v_i_883_, v___x_892_);
v_i_883_ = v___x_893_;
v_b_884_ = v_a_891_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(lean_object* v_f_935_, lean_object* v_args_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_fNew_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; 
switch(lean_obj_tag(v_f_935_))
{
case 4:
{
lean_object* v_declName_951_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___x_975_; lean_object* v_env_976_; uint8_t v_isExporting_977_; 
v_declName_951_ = lean_ctor_get(v_f_935_, 0);
v___x_975_ = lean_st_ref_get(v_a_940_);
v_env_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_ref(v_env_976_);
lean_dec(v___x_975_);
v_isExporting_977_ = lean_ctor_get_uint8(v_env_976_, sizeof(void*)*8);
lean_dec_ref(v_env_976_);
if (v_isExporting_977_ == 0)
{
v___y_953_ = v_a_937_;
v___y_954_ = v_a_938_;
v___y_955_ = v_a_939_;
v___y_956_ = v_a_940_;
goto v___jp_952_;
}
else
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_isPrivateName(v_declName_951_);
if (v___x_978_ == 0)
{
v___y_953_ = v_a_937_;
v___y_954_ = v_a_938_;
v___y_955_ = v_a_939_;
v___y_956_ = v_a_940_;
goto v___jp_952_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1);
v___x_980_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_979_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_dec_ref(v___x_980_);
v___y_953_ = v_a_937_;
v___y_954_ = v_a_938_;
v___y_955_ = v_a_939_;
v___y_956_ = v_a_940_;
goto v___jp_952_;
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v_f_935_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
v___jp_952_:
{
lean_object* v___x_957_; 
lean_inc_ref(v___y_955_);
lean_inc(v_declName_951_);
v___x_957_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_declName_951_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
if (lean_obj_tag(v_a_958_) == 5)
{
lean_dec_ref(v_a_958_);
lean_del_object(v___x_960_);
v_fNew_943_ = v_f_935_;
v___y_944_ = v___y_953_;
v___y_945_ = v___y_954_;
v___y_946_ = v___y_955_;
v___y_947_ = v___y_956_;
goto v___jp_942_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_964_; 
lean_dec(v_a_958_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v_f_935_);
v___x_962_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v_f_935_);
v_a_967_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_957_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_957_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
case 1:
{
v_fNew_943_ = v_f_935_;
v___y_944_ = v_a_937_;
v___y_945_ = v_a_938_;
v___y_946_ = v_a_939_;
v___y_947_ = v_a_940_;
goto v___jp_942_;
}
default: 
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec_ref(v_f_935_);
v___x_989_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
v___jp_942_:
{
size_t v_sz_948_; size_t v___x_949_; lean_object* v___x_950_; 
v_sz_948_ = lean_array_size(v_args_936_);
v___x_949_ = ((size_t)0ULL);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_args_936_, v_sz_948_, v___x_949_, v_fNew_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
if (lean_obj_tag(v_x_991_) == 5)
{
lean_object* v_fn_999_; lean_object* v_arg_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_fn_999_ = lean_ctor_get(v_x_991_, 0);
lean_inc_ref(v_fn_999_);
v_arg_1000_ = lean_ctor_get(v_x_991_, 1);
lean_inc_ref(v_arg_1000_);
lean_dec_ref(v_x_991_);
v___x_1001_ = lean_array_set(v_x_992_, v_x_993_, v_arg_1000_);
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_sub(v_x_993_, v___x_1002_);
lean_dec(v_x_993_);
v_x_991_ = v_fn_999_;
v_x_992_ = v___x_1001_;
v_x_993_ = v___x_1003_;
goto _start;
}
else
{
lean_object* v___x_1005_; 
lean_dec(v_x_993_);
v___x_1005_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_x_991_, v_x_992_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec_ref(v_x_992_);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0___boxed(lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_x_1006_, v_x_1007_, v_x_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___boxed(lean_object* v_e_1015_, lean_object* v_xs_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_e_1015_, v_xs_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___boxed(lean_object* v_f_1023_, lean_object* v_args_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_f_1023_, v_args_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
lean_dec_ref(v_args_1024_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3___boxed(lean_object* v_as_1031_, lean_object* v_sz_1032_, lean_object* v_i_1033_, lean_object* v_b_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
size_t v_sz_boxed_1040_; size_t v_i_boxed_1041_; lean_object* v_res_1042_; 
v_sz_boxed_1040_ = lean_unbox_usize(v_sz_1032_);
lean_dec(v_sz_1032_);
v_i_boxed_1041_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_res_1042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_as_1031_, v_sz_boxed_1040_, v_i_boxed_1041_, v_b_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec_ref(v_as_1031_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed(lean_object* v_type_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(lean_object* v_00_u03b1_1050_, lean_object* v_msg_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___boxed(lean_object* v_00_u03b1_1058_, lean_object* v_msg_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(v_00_u03b1_1058_, v_msg_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(lean_object* v_00_u03b1_1066_, lean_object* v_constName_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___boxed(lean_object* v_00_u03b1_1074_, lean_object* v_constName_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(v_00_u03b1_1074_, v_constName_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(lean_object* v_00_u03b1_1082_, lean_object* v_ref_1083_, lean_object* v_constName_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_1083_, v_constName_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1091_, lean_object* v_ref_1092_, lean_object* v_constName_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(v_00_u03b1_1091_, v_ref_1092_, v_constName_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v_ref_1092_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(lean_object* v_00_u03b1_1100_, lean_object* v_ref_1101_, lean_object* v_msg_1102_, lean_object* v_declHint_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_1101_, v_msg_1102_, v_declHint_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1110_, lean_object* v_ref_1111_, lean_object* v_msg_1112_, lean_object* v_declHint_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(v_00_u03b1_1110_, v_ref_1111_, v_msg_1112_, v_declHint_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v_ref_1111_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(lean_object* v_msg_1120_, lean_object* v_declHint_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1120_, v_declHint_1121_, v___y_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_1128_, lean_object* v_declHint_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(v_msg_1128_, v_declHint_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(lean_object* v_00_u03b1_1136_, lean_object* v_ref_1137_, lean_object* v_msg_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1137_, v_msg_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1145_, lean_object* v_ref_1146_, lean_object* v_msg_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(v_00_u03b1_1145_, v_ref_1146_, v_msg_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v_ref_1146_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(lean_object* v___y_1154_, uint8_t v_isExporting_1155_, lean_object* v___x_1156_, lean_object* v___y_1157_, lean_object* v___x_1158_, lean_object* v_a_x3f_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v_env_1162_; lean_object* v_nextMacroScope_1163_; lean_object* v_ngen_1164_; lean_object* v_auxDeclNGen_1165_; lean_object* v_traceState_1166_; lean_object* v_messages_1167_; lean_object* v_infoState_1168_; lean_object* v_snapshotTasks_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1194_; 
v___x_1161_ = lean_st_ref_take(v___y_1154_);
v_env_1162_ = lean_ctor_get(v___x_1161_, 0);
v_nextMacroScope_1163_ = lean_ctor_get(v___x_1161_, 1);
v_ngen_1164_ = lean_ctor_get(v___x_1161_, 2);
v_auxDeclNGen_1165_ = lean_ctor_get(v___x_1161_, 3);
v_traceState_1166_ = lean_ctor_get(v___x_1161_, 4);
v_messages_1167_ = lean_ctor_get(v___x_1161_, 6);
v_infoState_1168_ = lean_ctor_get(v___x_1161_, 7);
v_snapshotTasks_1169_ = lean_ctor_get(v___x_1161_, 8);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v___x_1161_, 5);
lean_dec(v_unused_1195_);
v___x_1171_ = v___x_1161_;
v_isShared_1172_ = v_isSharedCheck_1194_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_snapshotTasks_1169_);
lean_inc(v_infoState_1168_);
lean_inc(v_messages_1167_);
lean_inc(v_traceState_1166_);
lean_inc(v_auxDeclNGen_1165_);
lean_inc(v_ngen_1164_);
lean_inc(v_nextMacroScope_1163_);
lean_inc(v_env_1162_);
lean_dec(v___x_1161_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1194_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = l_Lean_Environment_setExporting(v_env_1162_, v_isExporting_1155_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 5, v___x_1156_);
lean_ctor_set(v___x_1171_, 0, v___x_1173_);
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_nextMacroScope_1163_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_ngen_1164_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_auxDeclNGen_1165_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_traceState_1166_);
lean_ctor_set(v_reuseFailAlloc_1193_, 5, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1193_, 6, v_messages_1167_);
lean_ctor_set(v_reuseFailAlloc_1193_, 7, v_infoState_1168_);
lean_ctor_set(v_reuseFailAlloc_1193_, 8, v_snapshotTasks_1169_);
v___x_1175_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_mctx_1178_; lean_object* v_zetaDeltaFVarIds_1179_; lean_object* v_postponed_1180_; lean_object* v_diag_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1191_; 
v___x_1176_ = lean_st_ref_set(v___y_1154_, v___x_1175_);
v___x_1177_ = lean_st_ref_take(v___y_1157_);
v_mctx_1178_ = lean_ctor_get(v___x_1177_, 0);
v_zetaDeltaFVarIds_1179_ = lean_ctor_get(v___x_1177_, 2);
v_postponed_1180_ = lean_ctor_get(v___x_1177_, 3);
v_diag_1181_ = lean_ctor_get(v___x_1177_, 4);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v___x_1177_, 1);
lean_dec(v_unused_1192_);
v___x_1183_ = v___x_1177_;
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_diag_1181_);
lean_inc(v_postponed_1180_);
lean_inc(v_zetaDeltaFVarIds_1179_);
lean_inc(v_mctx_1178_);
lean_dec(v___x_1177_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v___x_1158_);
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_mctx_1178_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_zetaDeltaFVarIds_1179_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_postponed_1180_);
lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_diag_1181_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = lean_st_ref_set(v___y_1157_, v___x_1186_);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0___boxed(lean_object* v___y_1196_, lean_object* v_isExporting_1197_, lean_object* v___x_1198_, lean_object* v___y_1199_, lean_object* v___x_1200_, lean_object* v_a_x3f_1201_, lean_object* v___y_1202_){
_start:
{
uint8_t v_isExporting_boxed_1203_; lean_object* v_res_1204_; 
v_isExporting_boxed_1203_ = lean_unbox(v_isExporting_1197_);
v_res_1204_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1196_, v_isExporting_boxed_1203_, v___x_1198_, v___y_1199_, v___x_1200_, v_a_x3f_1201_);
lean_dec(v_a_x3f_1201_);
lean_dec(v___y_1199_);
lean_dec(v___y_1196_);
return v_res_1204_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
v___x_1211_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
lean_ctor_set(v___x_1211_, 2, v___x_1210_);
lean_ctor_set(v___x_1211_, 3, v___x_1210_);
lean_ctor_set(v___x_1211_, 4, v___x_1210_);
lean_ctor_set(v___x_1211_, 5, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(lean_object* v_x_1212_, uint8_t v_isExporting_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v_env_1220_; uint8_t v_isExporting_1221_; lean_object* v___x_1222_; lean_object* v_env_1223_; lean_object* v_nextMacroScope_1224_; lean_object* v_ngen_1225_; lean_object* v_auxDeclNGen_1226_; lean_object* v_traceState_1227_; lean_object* v_messages_1228_; lean_object* v_infoState_1229_; lean_object* v_snapshotTasks_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1284_; 
v___x_1219_ = lean_st_ref_get(v___y_1217_);
v_env_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc_ref(v_env_1220_);
lean_dec(v___x_1219_);
v_isExporting_1221_ = lean_ctor_get_uint8(v_env_1220_, sizeof(void*)*8);
lean_dec_ref(v_env_1220_);
v___x_1222_ = lean_st_ref_take(v___y_1217_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
v_nextMacroScope_1224_ = lean_ctor_get(v___x_1222_, 1);
v_ngen_1225_ = lean_ctor_get(v___x_1222_, 2);
v_auxDeclNGen_1226_ = lean_ctor_get(v___x_1222_, 3);
v_traceState_1227_ = lean_ctor_get(v___x_1222_, 4);
v_messages_1228_ = lean_ctor_get(v___x_1222_, 6);
v_infoState_1229_ = lean_ctor_get(v___x_1222_, 7);
v_snapshotTasks_1230_ = lean_ctor_get(v___x_1222_, 8);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v___x_1222_, 5);
lean_dec(v_unused_1285_);
v___x_1232_ = v___x_1222_;
v_isShared_1233_ = v_isSharedCheck_1284_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_snapshotTasks_1230_);
lean_inc(v_infoState_1229_);
lean_inc(v_messages_1228_);
lean_inc(v_traceState_1227_);
lean_inc(v_auxDeclNGen_1226_);
lean_inc(v_ngen_1225_);
lean_inc(v_nextMacroScope_1224_);
lean_inc(v_env_1223_);
lean_dec(v___x_1222_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1284_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1234_ = l_Lean_Environment_setExporting(v_env_1223_, v_isExporting_1213_);
v___x_1235_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 5, v___x_1235_);
lean_ctor_set(v___x_1232_, 0, v___x_1234_);
v___x_1237_ = v___x_1232_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_nextMacroScope_1224_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_ngen_1225_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_auxDeclNGen_1226_);
lean_ctor_set(v_reuseFailAlloc_1283_, 4, v_traceState_1227_);
lean_ctor_set(v_reuseFailAlloc_1283_, 5, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1283_, 6, v_messages_1228_);
lean_ctor_set(v_reuseFailAlloc_1283_, 7, v_infoState_1229_);
lean_ctor_set(v_reuseFailAlloc_1283_, 8, v_snapshotTasks_1230_);
v___x_1237_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_mctx_1240_; lean_object* v_zetaDeltaFVarIds_1241_; lean_object* v_postponed_1242_; lean_object* v_diag_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1281_; 
v___x_1238_ = lean_st_ref_set(v___y_1217_, v___x_1237_);
v___x_1239_ = lean_st_ref_take(v___y_1215_);
v_mctx_1240_ = lean_ctor_get(v___x_1239_, 0);
v_zetaDeltaFVarIds_1241_ = lean_ctor_get(v___x_1239_, 2);
v_postponed_1242_ = lean_ctor_get(v___x_1239_, 3);
v_diag_1243_ = lean_ctor_get(v___x_1239_, 4);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1239_, 1);
lean_dec(v_unused_1282_);
v___x_1245_ = v___x_1239_;
v_isShared_1246_ = v_isSharedCheck_1281_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_diag_1243_);
lean_inc(v_postponed_1242_);
lean_inc(v_zetaDeltaFVarIds_1241_);
lean_inc(v_mctx_1240_);
lean_dec(v___x_1239_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1281_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1247_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_mctx_1240_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_zetaDeltaFVarIds_1241_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v_postponed_1242_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v_diag_1243_);
v___x_1249_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; lean_object* v_r_1251_; 
v___x_1250_ = lean_st_ref_set(v___y_1215_, v___x_1249_);
lean_inc(v___y_1217_);
lean_inc(v___y_1215_);
v_r_1251_ = lean_apply_5(v_x_1212_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, lean_box(0));
if (lean_obj_tag(v_r_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1268_; 
v_a_1252_ = lean_ctor_get(v_r_1251_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_r_1251_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1254_ = v_r_1251_;
v_isShared_1255_ = v_isSharedCheck_1268_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v_r_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1268_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
lean_inc(v_a_1252_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 1);
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
v___x_1258_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1217_, v_isExporting_1221_, v___x_1235_, v___y_1215_, v___x_1247_, v___x_1257_);
lean_dec_ref(v___x_1257_);
lean_dec(v___y_1215_);
lean_dec(v___y_1217_);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v___x_1258_, 0);
lean_dec(v_unused_1266_);
v___x_1260_ = v___x_1258_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_dec(v___x_1258_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v_a_1252_);
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1252_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
v_a_1269_ = lean_ctor_get(v_r_1251_, 0);
lean_inc(v_a_1269_);
lean_dec_ref(v_r_1251_);
v___x_1270_ = lean_box(0);
v___x_1271_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1217_, v_isExporting_1221_, v___x_1235_, v___y_1215_, v___x_1247_, v___x_1270_);
lean_dec(v___y_1215_);
lean_dec(v___y_1217_);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1271_, 0);
lean_dec(v_unused_1279_);
v___x_1273_ = v___x_1271_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_dec(v___x_1271_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 1);
lean_ctor_set(v___x_1273_, 0, v_a_1269_);
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1269_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___boxed(lean_object* v_x_1286_, lean_object* v_isExporting_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
uint8_t v_isExporting_boxed_1293_; lean_object* v_res_1294_; 
v_isExporting_boxed_1293_ = lean_unbox(v_isExporting_1287_);
v_res_1294_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1286_, v_isExporting_boxed_1293_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object* v_00_u03b1_1295_, lean_object* v_x_1296_, uint8_t v_isExporting_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1296_, v_isExporting_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___boxed(lean_object* v_00_u03b1_1304_, lean_object* v_x_1305_, lean_object* v_isExporting_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v_isExporting_boxed_1312_; lean_object* v_res_1313_; 
v_isExporting_boxed_1312_ = lean_unbox(v_isExporting_1306_);
v_res_1313_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(v_00_u03b1_1304_, v_x_1305_, v_isExporting_boxed_1312_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(lean_object* v_opts_1314_, lean_object* v_opt_1315_){
_start:
{
lean_object* v_name_1316_; lean_object* v_defValue_1317_; lean_object* v_map_1318_; lean_object* v___x_1319_; 
v_name_1316_ = lean_ctor_get(v_opt_1315_, 0);
v_defValue_1317_ = lean_ctor_get(v_opt_1315_, 1);
v_map_1318_ = lean_ctor_get(v_opts_1314_, 0);
v___x_1319_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1318_, v_name_1316_);
if (lean_obj_tag(v___x_1319_) == 0)
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_unbox(v_defValue_1317_);
return v___x_1320_;
}
else
{
lean_object* v_val_1321_; 
v_val_1321_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_val_1321_);
lean_dec_ref(v___x_1319_);
if (lean_obj_tag(v_val_1321_) == 1)
{
uint8_t v_v_1322_; 
v_v_1322_ = lean_ctor_get_uint8(v_val_1321_, 0);
lean_dec_ref(v_val_1321_);
return v_v_1322_;
}
else
{
uint8_t v___x_1323_; 
lean_dec(v_val_1321_);
v___x_1323_ = lean_unbox(v_defValue_1317_);
return v___x_1323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5___boxed(lean_object* v_opts_1324_, lean_object* v_opt_1325_){
_start:
{
uint8_t v_res_1326_; lean_object* v_r_1327_; 
v_res_1326_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v_opts_1324_, v_opt_1325_);
lean_dec_ref(v_opt_1325_);
lean_dec_ref(v_opts_1324_);
v_r_1327_ = lean_box(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(lean_object* v_opts_1328_, lean_object* v_opt_1329_){
_start:
{
lean_object* v_name_1330_; lean_object* v_defValue_1331_; lean_object* v_map_1332_; lean_object* v___x_1333_; 
v_name_1330_ = lean_ctor_get(v_opt_1329_, 0);
v_defValue_1331_ = lean_ctor_get(v_opt_1329_, 1);
v_map_1332_ = lean_ctor_get(v_opts_1328_, 0);
v___x_1333_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1332_, v_name_1330_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_inc(v_defValue_1331_);
return v_defValue_1331_;
}
else
{
lean_object* v_val_1334_; 
v_val_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_val_1334_);
lean_dec_ref(v___x_1333_);
if (lean_obj_tag(v_val_1334_) == 3)
{
lean_object* v_v_1335_; 
v_v_1335_ = lean_ctor_get(v_val_1334_, 0);
lean_inc(v_v_1335_);
lean_dec_ref(v_val_1334_);
return v_v_1335_;
}
else
{
lean_dec(v_val_1334_);
lean_inc(v_defValue_1331_);
return v_defValue_1331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6___boxed(lean_object* v_opts_1336_, lean_object* v_opt_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(v_opts_1336_, v_opt_1337_);
lean_dec_ref(v_opt_1337_);
lean_dec_ref(v_opts_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object* v_a_1339_, lean_object* v_diag_1340_, lean_object* v_a_x3f_1341_){
_start:
{
lean_object* v___x_1343_; lean_object* v_mctx_1344_; lean_object* v_cache_1345_; lean_object* v_zetaDeltaFVarIds_1346_; lean_object* v_postponed_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1357_; 
v___x_1343_ = lean_st_ref_take(v_a_1339_);
v_mctx_1344_ = lean_ctor_get(v___x_1343_, 0);
v_cache_1345_ = lean_ctor_get(v___x_1343_, 1);
v_zetaDeltaFVarIds_1346_ = lean_ctor_get(v___x_1343_, 2);
v_postponed_1347_ = lean_ctor_get(v___x_1343_, 3);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; 
v_unused_1358_ = lean_ctor_get(v___x_1343_, 4);
lean_dec(v_unused_1358_);
v___x_1349_ = v___x_1343_;
v_isShared_1350_ = v_isSharedCheck_1357_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_postponed_1347_);
lean_inc(v_zetaDeltaFVarIds_1346_);
lean_inc(v_cache_1345_);
lean_inc(v_mctx_1344_);
lean_dec(v___x_1343_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1357_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 4, v_diag_1340_);
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_mctx_1344_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_cache_1345_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_zetaDeltaFVarIds_1346_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_postponed_1347_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_diag_1340_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_st_ref_set(v_a_1339_, v___x_1352_);
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object* v_a_1359_, lean_object* v_diag_1360_, lean_object* v_a_x3f_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1359_, v_diag_1360_, v_a_x3f_1361_);
lean_dec(v_a_x3f_1361_);
lean_dec(v_a_1359_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0(lean_object* v_ps_1364_, lean_object* v_k_1365_, lean_object* v_v_1366_){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v_k_1365_);
lean_ctor_set(v___x_1367_, 1, v_v_1366_);
v___x_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v_ps_1364_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(lean_object* v_f_1369_, lean_object* v_keys_1370_, lean_object* v_vals_1371_, lean_object* v_i_1372_, lean_object* v_acc_1373_){
_start:
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_array_get_size(v_keys_1370_);
v___x_1375_ = lean_nat_dec_lt(v_i_1372_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_dec(v_i_1372_);
lean_dec(v_f_1369_);
return v_acc_1373_;
}
else
{
lean_object* v_k_1376_; lean_object* v_v_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_k_1376_ = lean_array_fget_borrowed(v_keys_1370_, v_i_1372_);
v_v_1377_ = lean_array_fget_borrowed(v_vals_1371_, v_i_1372_);
lean_inc(v_f_1369_);
lean_inc(v_v_1377_);
lean_inc(v_k_1376_);
v___x_1378_ = lean_apply_3(v_f_1369_, v_acc_1373_, v_k_1376_, v_v_1377_);
v___x_1379_ = lean_unsigned_to_nat(1u);
v___x_1380_ = lean_nat_add(v_i_1372_, v___x_1379_);
lean_dec(v_i_1372_);
v_i_1372_ = v___x_1380_;
v_acc_1373_ = v___x_1378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_f_1382_, lean_object* v_keys_1383_, lean_object* v_vals_1384_, lean_object* v_i_1385_, lean_object* v_acc_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1382_, v_keys_1383_, v_vals_1384_, v_i_1385_, v_acc_1386_);
lean_dec_ref(v_vals_1384_);
lean_dec_ref(v_keys_1383_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(lean_object* v_f_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
lean_object* v_es_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_es_1391_ = lean_ctor_get(v_x_1389_, 0);
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = lean_array_get_size(v_es_1391_);
v___x_1394_ = lean_nat_dec_lt(v___x_1392_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_dec(v_f_1388_);
return v_x_1390_;
}
else
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_nat_dec_le(v___x_1393_, v___x_1393_);
if (v___x_1395_ == 0)
{
if (v___x_1394_ == 0)
{
lean_dec(v_f_1388_);
return v_x_1390_;
}
else
{
size_t v___x_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = lean_usize_of_nat(v___x_1393_);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1388_, v_es_1391_, v___x_1396_, v___x_1397_, v_x_1390_);
return v___x_1398_;
}
}
else
{
size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = ((size_t)0ULL);
v___x_1400_ = lean_usize_of_nat(v___x_1393_);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1388_, v_es_1391_, v___x_1399_, v___x_1400_, v_x_1390_);
return v___x_1401_;
}
}
}
else
{
lean_object* v_ks_1402_; lean_object* v_vs_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_ks_1402_ = lean_ctor_get(v_x_1389_, 0);
v_vs_1403_ = lean_ctor_get(v_x_1389_, 1);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1388_, v_ks_1402_, v_vs_1403_, v___x_1404_, v_x_1390_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(lean_object* v_f_1406_, lean_object* v_as_1407_, size_t v_i_1408_, size_t v_stop_1409_, lean_object* v_b_1410_){
_start:
{
lean_object* v___y_1412_; uint8_t v___x_1416_; 
v___x_1416_ = lean_usize_dec_eq(v_i_1408_, v_stop_1409_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_array_uget_borrowed(v_as_1407_, v_i_1408_);
switch(lean_obj_tag(v___x_1417_))
{
case 0:
{
lean_object* v_key_1418_; lean_object* v_val_1419_; lean_object* v___x_1420_; 
v_key_1418_ = lean_ctor_get(v___x_1417_, 0);
v_val_1419_ = lean_ctor_get(v___x_1417_, 1);
lean_inc(v_f_1406_);
lean_inc(v_val_1419_);
lean_inc(v_key_1418_);
v___x_1420_ = lean_apply_3(v_f_1406_, v_b_1410_, v_key_1418_, v_val_1419_);
v___y_1412_ = v___x_1420_;
goto v___jp_1411_;
}
case 1:
{
lean_object* v_node_1421_; lean_object* v___x_1422_; 
v_node_1421_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_f_1406_);
v___x_1422_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1406_, v_node_1421_, v_b_1410_);
v___y_1412_ = v___x_1422_;
goto v___jp_1411_;
}
default: 
{
v___y_1412_ = v_b_1410_;
goto v___jp_1411_;
}
}
}
else
{
lean_dec(v_f_1406_);
return v_b_1410_;
}
v___jp_1411_:
{
size_t v___x_1413_; size_t v___x_1414_; 
v___x_1413_ = ((size_t)1ULL);
v___x_1414_ = lean_usize_add(v_i_1408_, v___x_1413_);
v_i_1408_ = v___x_1414_;
v_b_1410_ = v___y_1412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg___boxed(lean_object* v_f_1423_, lean_object* v_as_1424_, lean_object* v_i_1425_, lean_object* v_stop_1426_, lean_object* v_b_1427_){
_start:
{
size_t v_i_boxed_1428_; size_t v_stop_boxed_1429_; lean_object* v_res_1430_; 
v_i_boxed_1428_ = lean_unbox_usize(v_i_1425_);
lean_dec(v_i_1425_);
v_stop_boxed_1429_ = lean_unbox_usize(v_stop_1426_);
lean_dec(v_stop_1426_);
v_res_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1423_, v_as_1424_, v_i_boxed_1428_, v_stop_boxed_1429_, v_b_1427_);
lean_dec_ref(v_as_1424_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_f_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1431_, v_x_1432_, v_x_1433_);
lean_dec_ref(v_x_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0(lean_object* v_f_1435_, lean_object* v_x1_1436_, lean_object* v_x2_1437_, lean_object* v_x3_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_apply_3(v_f_1435_, v_x1_1436_, v_x2_1437_, v_x3_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(lean_object* v_map_1440_, lean_object* v_f_1441_, lean_object* v_init_1442_){
_start:
{
lean_object* v___f_1443_; lean_object* v___x_1444_; 
v___f_1443_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1443_, 0, v_f_1441_);
v___x_1444_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v___f_1443_, v_map_1440_, v_init_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___boxed(lean_object* v_map_1445_, lean_object* v_f_1446_, lean_object* v_init_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_1445_, v_f_1446_, v_init_1447_);
lean_dec_ref(v_map_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(lean_object* v_m_1450_){
_start:
{
lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___f_1451_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0));
v___x_1452_ = lean_box(0);
v___x_1453_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_m_1450_, v___f_1451_, v___x_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___boxed(lean_object* v_m_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1454_);
lean_dec_ref(v_m_1454_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(lean_object* v_o_1459_, lean_object* v_k_1460_, uint8_t v_v_1461_){
_start:
{
lean_object* v_map_1462_; uint8_t v_hasTrace_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1477_; 
v_map_1462_ = lean_ctor_get(v_o_1459_, 0);
v_hasTrace_1463_ = lean_ctor_get_uint8(v_o_1459_, sizeof(void*)*1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_o_1459_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1465_ = v_o_1459_;
v_isShared_1466_ = v_isSharedCheck_1477_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_map_1462_);
lean_dec(v_o_1459_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1477_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1467_, 0, v_v_1461_);
lean_inc(v_k_1460_);
v___x_1468_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1460_, v___x_1467_, v_map_1462_);
if (v_hasTrace_1463_ == 0)
{
lean_object* v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1472_; 
v___x_1469_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1));
v___x_1470_ = l_Lean_Name_isPrefixOf(v___x_1469_, v_k_1460_);
lean_dec(v_k_1460_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1468_);
v___x_1472_ = v___x_1465_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1468_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*1, v___x_1470_);
return v___x_1472_;
}
}
else
{
lean_object* v___x_1475_; 
lean_dec(v_k_1460_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1468_);
v___x_1475_ = v___x_1465_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1468_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*1, v_hasTrace_1463_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___boxed(lean_object* v_o_1478_, lean_object* v_k_1479_, lean_object* v_v_1480_){
_start:
{
uint8_t v_v_boxed_1481_; lean_object* v_res_1482_; 
v_v_boxed_1481_ = lean_unbox(v_v_1480_);
v_res_1482_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(v_o_1478_, v_k_1479_, v_v_boxed_1481_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(lean_object* v_opts_1483_, lean_object* v_opt_1484_, uint8_t v_val_1485_){
_start:
{
lean_object* v_name_1486_; lean_object* v___x_1487_; 
v_name_1486_ = lean_ctor_get(v_opt_1484_, 0);
lean_inc(v_name_1486_);
lean_dec_ref(v_opt_1484_);
v___x_1487_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(v_opts_1483_, v_name_1486_, v_val_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4___boxed(lean_object* v_opts_1488_, lean_object* v_opt_1489_, lean_object* v_val_1490_){
_start:
{
uint8_t v_val_boxed_1491_; lean_object* v_res_1492_; 
v_val_boxed_1491_ = lean_unbox(v_val_1490_);
v_res_1492_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v_opts_1488_, v_opt_1489_, v_val_boxed_1491_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(lean_object* v_keys_1493_, lean_object* v_vals_1494_, lean_object* v_i_1495_, lean_object* v_k_1496_){
_start:
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = lean_array_get_size(v_keys_1493_);
v___x_1498_ = lean_nat_dec_lt(v_i_1495_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v_i_1495_);
v___x_1499_ = lean_box(0);
return v___x_1499_;
}
else
{
lean_object* v_k_x27_1500_; uint8_t v___x_1501_; 
v_k_x27_1500_ = lean_array_fget_borrowed(v_keys_1493_, v_i_1495_);
v___x_1501_ = lean_name_eq(v_k_1496_, v_k_x27_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_unsigned_to_nat(1u);
v___x_1503_ = lean_nat_add(v_i_1495_, v___x_1502_);
lean_dec(v_i_1495_);
v_i_1495_ = v___x_1503_;
goto _start;
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_array_fget_borrowed(v_vals_1494_, v_i_1495_);
lean_dec(v_i_1495_);
lean_inc(v___x_1505_);
v___x_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_keys_1507_, lean_object* v_vals_1508_, lean_object* v_i_1509_, lean_object* v_k_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_keys_1507_, v_vals_1508_, v_i_1509_, v_k_1510_);
lean_dec(v_k_1510_);
lean_dec_ref(v_vals_1508_);
lean_dec_ref(v_keys_1507_);
return v_res_1511_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; 
v___x_1512_ = ((size_t)5ULL);
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_shift_left(v___x_1513_, v___x_1512_);
return v___x_1514_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1515_; size_t v___x_1516_; size_t v___x_1517_; 
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0);
v___x_1517_ = lean_usize_sub(v___x_1516_, v___x_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(lean_object* v_x_1518_, size_t v_x_1519_, lean_object* v_x_1520_){
_start:
{
if (lean_obj_tag(v_x_1518_) == 0)
{
lean_object* v_es_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1542_; 
v_es_1521_ = lean_ctor_get(v_x_1518_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_x_1518_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1523_ = v_x_1518_;
v_isShared_1524_ = v_isSharedCheck_1542_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_es_1521_);
lean_dec(v_x_1518_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1542_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; lean_object* v_j_1529_; lean_object* v___x_1530_; 
v___x_1525_ = lean_box(2);
v___x_1526_ = ((size_t)5ULL);
v___x_1527_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1);
v___x_1528_ = lean_usize_land(v_x_1519_, v___x_1527_);
v_j_1529_ = lean_usize_to_nat(v___x_1528_);
v___x_1530_ = lean_array_get(v___x_1525_, v_es_1521_, v_j_1529_);
lean_dec(v_j_1529_);
lean_dec_ref(v_es_1521_);
switch(lean_obj_tag(v___x_1530_))
{
case 0:
{
lean_object* v_key_1531_; lean_object* v_val_1532_; uint8_t v___x_1533_; 
v_key_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_key_1531_);
v_val_1532_ = lean_ctor_get(v___x_1530_, 1);
lean_inc(v_val_1532_);
lean_dec_ref(v___x_1530_);
v___x_1533_ = lean_name_eq(v_x_1520_, v_key_1531_);
lean_dec(v_key_1531_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_dec(v_val_1532_);
lean_del_object(v___x_1523_);
v___x_1534_ = lean_box(0);
return v___x_1534_;
}
else
{
lean_object* v___x_1536_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set_tag(v___x_1523_, 1);
lean_ctor_set(v___x_1523_, 0, v_val_1532_);
v___x_1536_ = v___x_1523_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_val_1532_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
case 1:
{
lean_object* v_node_1538_; size_t v___x_1539_; 
lean_del_object(v___x_1523_);
v_node_1538_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_node_1538_);
lean_dec_ref(v___x_1530_);
v___x_1539_ = lean_usize_shift_right(v_x_1519_, v___x_1526_);
v_x_1518_ = v_node_1538_;
v_x_1519_ = v___x_1539_;
goto _start;
}
default: 
{
lean_object* v___x_1541_; 
lean_del_object(v___x_1523_);
v___x_1541_ = lean_box(0);
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_ks_1543_; lean_object* v_vs_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_ks_1543_ = lean_ctor_get(v_x_1518_, 0);
lean_inc_ref(v_ks_1543_);
v_vs_1544_ = lean_ctor_get(v_x_1518_, 1);
lean_inc_ref(v_vs_1544_);
lean_dec_ref(v_x_1518_);
v___x_1545_ = lean_unsigned_to_nat(0u);
v___x_1546_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_ks_1543_, v_vs_1544_, v___x_1545_, v_x_1520_);
lean_dec_ref(v_vs_1544_);
lean_dec_ref(v_ks_1543_);
return v___x_1546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___boxed(lean_object* v_x_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_){
_start:
{
size_t v_x_20265__boxed_1550_; lean_object* v_res_1551_; 
v_x_20265__boxed_1550_ = lean_unbox_usize(v_x_1548_);
lean_dec(v_x_1548_);
v_res_1551_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1547_, v_x_20265__boxed_1550_, v_x_1549_);
lean_dec(v_x_1549_);
return v_res_1551_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1552_; uint64_t v___x_1553_; 
v___x_1552_ = lean_unsigned_to_nat(1723u);
v___x_1553_ = lean_uint64_of_nat(v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(lean_object* v_x_1554_, lean_object* v_x_1555_){
_start:
{
uint64_t v___y_1557_; 
if (lean_obj_tag(v_x_1555_) == 0)
{
uint64_t v___x_1560_; 
v___x_1560_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0);
v___y_1557_ = v___x_1560_;
goto v___jp_1556_;
}
else
{
uint64_t v_hash_1561_; 
v_hash_1561_ = lean_ctor_get_uint64(v_x_1555_, sizeof(void*)*2);
v___y_1557_ = v_hash_1561_;
goto v___jp_1556_;
}
v___jp_1556_:
{
size_t v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_uint64_to_usize(v___y_1557_);
v___x_1559_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1554_, v___x_1558_, v_x_1555_);
return v___x_1559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___boxed(lean_object* v_x_1562_, lean_object* v_x_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1562_, v_x_1563_);
lean_dec(v_x_1563_);
return v_res_1564_;
}
}
static lean_object* _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(lean_object* v___x_1568_, uint8_t v___x_1569_, lean_object* v___x_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
if (lean_obj_tag(v_a_1571_) == 0)
{
lean_object* v___x_1573_; 
lean_dec_ref(v___x_1570_);
lean_dec_ref(v___x_1568_);
v___x_1573_ = lean_array_to_list(v_a_1572_);
return v___x_1573_;
}
else
{
lean_object* v_head_1574_; lean_object* v_tail_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1615_; 
v_head_1574_ = lean_ctor_get(v_a_1571_, 0);
v_tail_1575_ = lean_ctor_get(v_a_1571_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_a_1571_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1577_ = v_a_1571_;
v_isShared_1578_ = v_isSharedCheck_1615_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_tail_1575_);
lean_inc(v_head_1574_);
lean_dec(v_a_1571_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1615_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v_fst_1579_; lean_object* v_snd_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1614_; 
v_fst_1579_ = lean_ctor_get(v_head_1574_, 0);
v_snd_1580_ = lean_ctor_get(v_head_1574_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_head_1574_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1582_ = v_head_1574_;
v_isShared_1583_ = v_isSharedCheck_1614_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_snd_1580_);
lean_inc(v_fst_1579_);
lean_dec(v_head_1574_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1614_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___y_1585_; lean_object* v___y_1600_; uint8_t v___y_1601_; lean_object* v_unfoldAxiomCounter_1603_; lean_object* v___x_1604_; lean_object* v___y_1606_; lean_object* v___x_1612_; 
v_unfoldAxiomCounter_1603_ = lean_ctor_get(v___x_1568_, 1);
v___x_1604_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_unfoldAxiomCounter_1603_);
v___x_1612_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_unfoldAxiomCounter_1603_, v_fst_1579_);
if (lean_obj_tag(v___x_1612_) == 0)
{
v___y_1606_ = v___x_1604_;
goto v___jp_1605_;
}
else
{
lean_object* v_val_1613_; 
v_val_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_val_1613_);
lean_dec_ref(v___x_1612_);
v___y_1606_ = v_val_1613_;
goto v___jp_1605_;
}
v___jp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1586_ = l_Lean_MessageData_ofConstName(v_fst_1579_, v___x_1569_);
v___x_1587_ = lean_obj_once(&l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1, &l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1_once, _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1);
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 7);
lean_ctor_set(v___x_1582_, 1, v___x_1587_);
lean_ctor_set(v___x_1582_, 0, v___x_1586_);
v___x_1589_ = v___x_1582_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1590_ = l_Nat_reprFast(v___y_1585_);
v___x_1591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
v___x_1592_ = l_Lean_MessageData_ofFormat(v___x_1591_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 7);
lean_ctor_set(v___x_1577_, 1, v___x_1592_);
lean_ctor_set(v___x_1577_, 0, v___x_1589_);
v___x_1594_ = v___x_1577_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_array_push(v_a_1572_, v___x_1594_);
v_a_1571_ = v_tail_1575_;
v_a_1572_ = v___x_1595_;
goto _start;
}
}
}
v___jp_1599_:
{
if (v___y_1601_ == 0)
{
lean_dec(v___y_1600_);
lean_del_object(v___x_1582_);
lean_dec(v_fst_1579_);
lean_del_object(v___x_1577_);
v_a_1571_ = v_tail_1575_;
goto _start;
}
else
{
v___y_1585_ = v___y_1600_;
goto v___jp_1584_;
}
}
v___jp_1605_:
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = lean_nat_sub(v_snd_1580_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec(v_snd_1580_);
v___x_1608_ = lean_nat_dec_lt(v___x_1604_, v___x_1607_);
if (v___x_1608_ == 0)
{
v___y_1600_ = v___x_1607_;
v___y_1601_ = v___x_1608_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1609_; 
lean_inc(v_fst_1579_);
lean_inc_ref(v___x_1570_);
v___x_1609_ = l_Lean_getOriginalConstKind_x3f(v___x_1570_, v_fst_1579_);
if (lean_obj_tag(v___x_1609_) == 1)
{
lean_object* v_val_1610_; uint8_t v___x_1611_; 
v_val_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_val_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = lean_unbox(v_val_1610_);
lean_dec(v_val_1610_);
if (v___x_1611_ == 0)
{
v___y_1585_ = v___x_1607_;
goto v___jp_1584_;
}
else
{
v___y_1600_ = v___x_1607_;
v___y_1601_ = v___x_1569_;
goto v___jp_1599_;
}
}
else
{
lean_dec(v___x_1609_);
v___y_1600_ = v___x_1607_;
v___y_1601_ = v___x_1569_;
goto v___jp_1599_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___boxed(lean_object* v___x_1616_, lean_object* v___x_1617_, lean_object* v___x_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
uint8_t v___x_20358__boxed_1621_; lean_object* v_res_1622_; 
v___x_20358__boxed_1621_ = lean_unbox(v___x_1617_);
v_res_1622_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v___x_1616_, v___x_20358__boxed_1621_, v___x_1618_, v_a_1619_, v_a_1620_);
return v_res_1622_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__0));
v___x_1625_ = l_Lean_stringToMessageData(v___x_1624_);
return v___x_1625_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__2));
v___x_1628_ = l_Lean_stringToMessageData(v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__4));
v___x_1631_ = l_Lean_stringToMessageData(v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__6));
v___x_1634_ = l_Lean_stringToMessageData(v___x_1633_);
return v___x_1634_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__8));
v___x_1637_ = l_Lean_stringToMessageData(v___x_1636_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__11));
v___x_1642_ = l_Lean_stringToMessageData(v___x_1641_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_box(1);
v___x_1644_ = l_Lean_MessageData_ofFormat(v___x_1643_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__14));
v___x_1647_ = l_Lean_stringToMessageData(v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object* v_type_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_inc_ref(v_type_1648_);
v___x_1654_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed), 6, 1);
lean_closure_set(v___x_1654_, 0, v_type_1648_);
lean_inc(v_a_1652_);
lean_inc_ref(v_a_1651_);
lean_inc(v_a_1650_);
lean_inc_ref(v_a_1649_);
v___x_1655_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1826_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1826_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1826_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v_env_1661_; lean_object* v___x_1662_; uint8_t v_isModule_1663_; 
v___x_1660_ = lean_st_ref_get(v_a_1652_);
v_env_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc_ref(v_env_1661_);
lean_dec(v___x_1660_);
v___x_1662_ = l_Lean_Environment_header(v_env_1661_);
lean_dec_ref(v_env_1661_);
v_isModule_1663_ = lean_ctor_get_uint8(v___x_1662_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1662_);
if (v_isModule_1663_ == 0)
{
lean_object* v___x_1665_; 
lean_dec_ref(v___x_1654_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
if (v_isShared_1659_ == 0)
{
v___x_1665_ = v___x_1658_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1656_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
else
{
lean_object* v___x_1667_; 
lean_del_object(v___x_1658_);
lean_inc(v_a_1652_);
lean_inc_ref(v_a_1651_);
lean_inc(v_a_1650_);
lean_inc_ref(v_a_1649_);
lean_inc_ref(v___x_1654_);
v___x_1667_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1654_, v_isModule_1663_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1812_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1812_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1812_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_expr_eqv(v_a_1656_, v_a_1668_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v_diag_1675_; lean_object* v_fileName_1676_; lean_object* v_fileMap_1677_; lean_object* v_options_1678_; lean_object* v_currRecDepth_1679_; lean_object* v_ref_1680_; lean_object* v_currNamespace_1681_; lean_object* v_openDecls_1682_; lean_object* v_initHeartbeats_1683_; lean_object* v_maxHeartbeats_1684_; lean_object* v_quotContext_1685_; lean_object* v_currMacroScope_1686_; lean_object* v_cancelTk_x3f_1687_; uint8_t v_suppressElabErrors_1688_; lean_object* v_inheritedTraceOptions_1689_; lean_object* v_env_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v_a_1705_; lean_object* v___y_1751_; uint8_t v___y_1752_; uint8_t v___x_1763_; lean_object* v_fileName_1765_; lean_object* v_fileMap_1766_; lean_object* v_currRecDepth_1767_; lean_object* v_ref_1768_; lean_object* v_currNamespace_1769_; lean_object* v_openDecls_1770_; lean_object* v_initHeartbeats_1771_; lean_object* v_maxHeartbeats_1772_; lean_object* v_quotContext_1773_; lean_object* v_currMacroScope_1774_; lean_object* v_cancelTk_x3f_1775_; uint8_t v_suppressElabErrors_1776_; lean_object* v_inheritedTraceOptions_1777_; lean_object* v___y_1778_; uint8_t v___y_1787_; uint8_t v___x_1808_; 
lean_del_object(v___x_1670_);
v___x_1673_ = lean_st_ref_get(v_a_1650_);
v___x_1674_ = lean_st_ref_get(v_a_1652_);
v_diag_1675_ = lean_ctor_get(v___x_1673_, 4);
lean_inc_ref(v_diag_1675_);
lean_dec(v___x_1673_);
v_fileName_1676_ = lean_ctor_get(v_a_1651_, 0);
v_fileMap_1677_ = lean_ctor_get(v_a_1651_, 1);
v_options_1678_ = lean_ctor_get(v_a_1651_, 2);
v_currRecDepth_1679_ = lean_ctor_get(v_a_1651_, 3);
v_ref_1680_ = lean_ctor_get(v_a_1651_, 5);
v_currNamespace_1681_ = lean_ctor_get(v_a_1651_, 6);
v_openDecls_1682_ = lean_ctor_get(v_a_1651_, 7);
v_initHeartbeats_1683_ = lean_ctor_get(v_a_1651_, 8);
v_maxHeartbeats_1684_ = lean_ctor_get(v_a_1651_, 9);
v_quotContext_1685_ = lean_ctor_get(v_a_1651_, 10);
v_currMacroScope_1686_ = lean_ctor_get(v_a_1651_, 11);
v_cancelTk_x3f_1687_ = lean_ctor_get(v_a_1651_, 12);
v_suppressElabErrors_1688_ = lean_ctor_get_uint8(v_a_1651_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1689_ = lean_ctor_get(v_a_1651_, 13);
v_env_1690_ = lean_ctor_get(v___x_1674_, 0);
lean_inc_ref(v_env_1690_);
lean_dec(v___x_1674_);
v___x_1691_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1678_);
v___x_1692_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v_options_1678_, v___x_1691_, v_isModule_1663_);
v___x_1693_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__1, &l_Lean_Compiler_LCNF_toLCNFType___closed__1_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1);
v___x_1694_ = l_Lean_MessageData_ofExpr(v_a_1656_);
v___x_1695_ = l_Lean_indentD(v___x_1694_);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1693_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__3, &l_Lean_Compiler_LCNF_toLCNFType___closed__3_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = l_Lean_MessageData_ofExpr(v_a_1668_);
v___x_1700_ = l_Lean_indentD(v___x_1699_);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1698_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__5, &l_Lean_Compiler_LCNF_toLCNFType___closed__5_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1763_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v___x_1692_, v___x_1691_);
v___x_1808_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1690_);
lean_dec_ref(v_env_1690_);
if (v___x_1808_ == 0)
{
if (v___x_1763_ == 0)
{
lean_inc(v_a_1652_);
lean_inc_ref(v_inheritedTraceOptions_1689_);
lean_inc(v_cancelTk_x3f_1687_);
lean_inc(v_currMacroScope_1686_);
lean_inc(v_quotContext_1685_);
lean_inc(v_maxHeartbeats_1684_);
lean_inc(v_initHeartbeats_1683_);
lean_inc(v_openDecls_1682_);
lean_inc(v_currNamespace_1681_);
lean_inc(v_ref_1680_);
lean_inc(v_currRecDepth_1679_);
lean_inc_ref(v_fileMap_1677_);
lean_inc_ref(v_fileName_1676_);
v_fileName_1765_ = v_fileName_1676_;
v_fileMap_1766_ = v_fileMap_1677_;
v_currRecDepth_1767_ = v_currRecDepth_1679_;
v_ref_1768_ = v_ref_1680_;
v_currNamespace_1769_ = v_currNamespace_1681_;
v_openDecls_1770_ = v_openDecls_1682_;
v_initHeartbeats_1771_ = v_initHeartbeats_1683_;
v_maxHeartbeats_1772_ = v_maxHeartbeats_1684_;
v_quotContext_1773_ = v_quotContext_1685_;
v_currMacroScope_1774_ = v_currMacroScope_1686_;
v_cancelTk_x3f_1775_ = v_cancelTk_x3f_1687_;
v_suppressElabErrors_1776_ = v_suppressElabErrors_1688_;
v_inheritedTraceOptions_1777_ = v_inheritedTraceOptions_1689_;
v___y_1778_ = v_a_1652_;
goto v___jp_1764_;
}
else
{
v___y_1787_ = v___x_1808_;
goto v___jp_1786_;
}
}
else
{
v___y_1787_ = v___x_1763_;
goto v___jp_1786_;
}
v___jp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v_snd_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1727_; 
lean_inc_ref(v_a_1705_);
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1705_);
v___x_1707_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1650_, v_diag_1675_, v___x_1706_);
lean_dec_ref(v___x_1706_);
lean_dec_ref(v___x_1707_);
v_snd_1708_ = lean_ctor_get(v_a_1705_, 1);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_a_1705_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v_a_1705_, 0);
lean_dec(v_unused_1728_);
v___x_1710_ = v_a_1705_;
v_isShared_1711_ = v_isSharedCheck_1727_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_snd_1708_);
lean_dec(v_a_1705_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1727_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__7, &l_Lean_Compiler_LCNF_toLCNFType___closed__7_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7);
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 7);
lean_ctor_set(v___x_1710_, 0, v___x_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_snd_1708_);
v___x_1714_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v___x_1715_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__9, &l_Lean_Compiler_LCNF_toLCNFType___closed__9_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9);
v___x_1716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_1716_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
v___jp_1729_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v_diag_1732_; lean_object* v_env_1733_; lean_object* v_unfoldAxiomCounter_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1730_ = lean_st_ref_get(v_a_1652_);
v___x_1731_ = lean_st_ref_get(v_a_1650_);
v_diag_1732_ = lean_ctor_get(v___x_1731_, 4);
lean_inc_ref(v_diag_1732_);
lean_dec(v___x_1731_);
v_env_1733_ = lean_ctor_get(v___x_1730_, 0);
lean_inc_ref(v_env_1733_);
lean_dec(v___x_1730_);
v_unfoldAxiomCounter_1734_ = lean_ctor_get(v_diag_1732_, 1);
lean_inc_ref(v_unfoldAxiomCounter_1734_);
lean_dec_ref(v_diag_1732_);
v___x_1735_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_unfoldAxiomCounter_1734_);
lean_dec_ref(v_unfoldAxiomCounter_1734_);
v___x_1736_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__10));
lean_inc_ref(v_diag_1675_);
v___x_1737_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v_diag_1675_, v___x_1672_, v_env_1733_, v___x_1735_, v___x_1736_);
v___x_1738_ = l_List_isEmpty___redArg(v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref(v___x_1703_);
v___x_1739_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__12, &l_Lean_Compiler_LCNF_toLCNFType___closed__12_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12);
v___x_1740_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__13, &l_Lean_Compiler_LCNF_toLCNFType___closed__13_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13);
v___x_1741_ = l_Lean_MessageData_joinSep(v___x_1737_, v___x_1740_);
v___x_1742_ = l_Lean_indentD(v___x_1741_);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1739_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__15, &l_Lean_Compiler_LCNF_toLCNFType___closed__15_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = lean_box(0);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v___x_1745_);
v_a_1705_ = v___x_1747_;
goto v___jp_1704_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v___x_1737_);
v___x_1748_ = lean_box(0);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
lean_ctor_set(v___x_1749_, 1, v___x_1703_);
v_a_1705_ = v___x_1749_;
goto v___jp_1704_;
}
}
v___jp_1750_:
{
if (v___y_1752_ == 0)
{
lean_dec_ref(v___y_1751_);
goto v___jp_1729_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v___x_1703_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec_ref(v_a_1649_);
v___x_1753_ = lean_box(0);
v___x_1754_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1650_, v_diag_1675_, v___x_1753_);
lean_dec(v_a_1650_);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v___x_1754_, 0);
lean_dec(v_unused_1762_);
v___x_1756_ = v___x_1754_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_dec(v___x_1754_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 1);
lean_ctor_set(v___x_1756_, 0, v___y_1751_);
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___y_1751_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
v___jp_1764_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1779_ = l_Lean_maxRecDepth;
v___x_1780_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(v___x_1692_, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1781_, 0, v_fileName_1765_);
lean_ctor_set(v___x_1781_, 1, v_fileMap_1766_);
lean_ctor_set(v___x_1781_, 2, v___x_1692_);
lean_ctor_set(v___x_1781_, 3, v_currRecDepth_1767_);
lean_ctor_set(v___x_1781_, 4, v___x_1780_);
lean_ctor_set(v___x_1781_, 5, v_ref_1768_);
lean_ctor_set(v___x_1781_, 6, v_currNamespace_1769_);
lean_ctor_set(v___x_1781_, 7, v_openDecls_1770_);
lean_ctor_set(v___x_1781_, 8, v_initHeartbeats_1771_);
lean_ctor_set(v___x_1781_, 9, v_maxHeartbeats_1772_);
lean_ctor_set(v___x_1781_, 10, v_quotContext_1773_);
lean_ctor_set(v___x_1781_, 11, v_currMacroScope_1774_);
lean_ctor_set(v___x_1781_, 12, v_cancelTk_x3f_1775_);
lean_ctor_set(v___x_1781_, 13, v_inheritedTraceOptions_1777_);
lean_ctor_set_uint8(v___x_1781_, sizeof(void*)*14, v___x_1763_);
lean_ctor_set_uint8(v___x_1781_, sizeof(void*)*14 + 1, v_suppressElabErrors_1776_);
lean_inc(v_a_1650_);
lean_inc_ref(v_a_1649_);
v___x_1782_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1654_, v_isModule_1663_, v_a_1649_, v_a_1650_, v___x_1781_, v___y_1778_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_dec_ref(v___x_1782_);
goto v___jp_1729_;
}
else
{
lean_object* v_a_1783_; uint8_t v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = l_Lean_Exception_isInterrupt(v_a_1783_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
lean_inc(v_a_1783_);
v___x_1785_ = l_Lean_Exception_isRuntime(v_a_1783_);
v___y_1751_ = v_a_1783_;
v___y_1752_ = v___x_1785_;
goto v___jp_1750_;
}
else
{
v___y_1751_ = v_a_1783_;
v___y_1752_ = v___x_1784_;
goto v___jp_1750_;
}
}
}
v___jp_1786_:
{
if (v___y_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v_env_1789_; lean_object* v_nextMacroScope_1790_; lean_object* v_ngen_1791_; lean_object* v_auxDeclNGen_1792_; lean_object* v_traceState_1793_; lean_object* v_messages_1794_; lean_object* v_infoState_1795_; lean_object* v_snapshotTasks_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1806_; 
v___x_1788_ = lean_st_ref_take(v_a_1652_);
v_env_1789_ = lean_ctor_get(v___x_1788_, 0);
v_nextMacroScope_1790_ = lean_ctor_get(v___x_1788_, 1);
v_ngen_1791_ = lean_ctor_get(v___x_1788_, 2);
v_auxDeclNGen_1792_ = lean_ctor_get(v___x_1788_, 3);
v_traceState_1793_ = lean_ctor_get(v___x_1788_, 4);
v_messages_1794_ = lean_ctor_get(v___x_1788_, 6);
v_infoState_1795_ = lean_ctor_get(v___x_1788_, 7);
v_snapshotTasks_1796_ = lean_ctor_get(v___x_1788_, 8);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v___x_1788_, 5);
lean_dec(v_unused_1807_);
v___x_1798_ = v___x_1788_;
v_isShared_1799_ = v_isSharedCheck_1806_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_snapshotTasks_1796_);
lean_inc(v_infoState_1795_);
lean_inc(v_messages_1794_);
lean_inc(v_traceState_1793_);
lean_inc(v_auxDeclNGen_1792_);
lean_inc(v_ngen_1791_);
lean_inc(v_nextMacroScope_1790_);
lean_inc(v_env_1789_);
lean_dec(v___x_1788_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1806_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1800_ = l_Lean_Kernel_enableDiag(v_env_1789_, v___x_1763_);
v___x_1801_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 5, v___x_1801_);
lean_ctor_set(v___x_1798_, 0, v___x_1800_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_nextMacroScope_1790_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v_ngen_1791_);
lean_ctor_set(v_reuseFailAlloc_1805_, 3, v_auxDeclNGen_1792_);
lean_ctor_set(v_reuseFailAlloc_1805_, 4, v_traceState_1793_);
lean_ctor_set(v_reuseFailAlloc_1805_, 5, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1805_, 6, v_messages_1794_);
lean_ctor_set(v_reuseFailAlloc_1805_, 7, v_infoState_1795_);
lean_ctor_set(v_reuseFailAlloc_1805_, 8, v_snapshotTasks_1796_);
v___x_1803_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_st_ref_set(v_a_1652_, v___x_1803_);
lean_inc(v_a_1652_);
lean_inc_ref(v_inheritedTraceOptions_1689_);
lean_inc(v_cancelTk_x3f_1687_);
lean_inc(v_currMacroScope_1686_);
lean_inc(v_quotContext_1685_);
lean_inc(v_maxHeartbeats_1684_);
lean_inc(v_initHeartbeats_1683_);
lean_inc(v_openDecls_1682_);
lean_inc(v_currNamespace_1681_);
lean_inc(v_ref_1680_);
lean_inc(v_currRecDepth_1679_);
lean_inc_ref(v_fileMap_1677_);
lean_inc_ref(v_fileName_1676_);
v_fileName_1765_ = v_fileName_1676_;
v_fileMap_1766_ = v_fileMap_1677_;
v_currRecDepth_1767_ = v_currRecDepth_1679_;
v_ref_1768_ = v_ref_1680_;
v_currNamespace_1769_ = v_currNamespace_1681_;
v_openDecls_1770_ = v_openDecls_1682_;
v_initHeartbeats_1771_ = v_initHeartbeats_1683_;
v_maxHeartbeats_1772_ = v_maxHeartbeats_1684_;
v_quotContext_1773_ = v_quotContext_1685_;
v_currMacroScope_1774_ = v_currMacroScope_1686_;
v_cancelTk_x3f_1775_ = v_cancelTk_x3f_1687_;
v_suppressElabErrors_1776_ = v_suppressElabErrors_1688_;
v_inheritedTraceOptions_1777_ = v_inheritedTraceOptions_1689_;
v___y_1778_ = v_a_1652_;
goto v___jp_1764_;
}
}
}
else
{
lean_inc(v_a_1652_);
lean_inc_ref(v_inheritedTraceOptions_1689_);
lean_inc(v_cancelTk_x3f_1687_);
lean_inc(v_currMacroScope_1686_);
lean_inc(v_quotContext_1685_);
lean_inc(v_maxHeartbeats_1684_);
lean_inc(v_initHeartbeats_1683_);
lean_inc(v_openDecls_1682_);
lean_inc(v_currNamespace_1681_);
lean_inc(v_ref_1680_);
lean_inc(v_currRecDepth_1679_);
lean_inc_ref(v_fileMap_1677_);
lean_inc_ref(v_fileName_1676_);
v_fileName_1765_ = v_fileName_1676_;
v_fileMap_1766_ = v_fileMap_1677_;
v_currRecDepth_1767_ = v_currRecDepth_1679_;
v_ref_1768_ = v_ref_1680_;
v_currNamespace_1769_ = v_currNamespace_1681_;
v_openDecls_1770_ = v_openDecls_1682_;
v_initHeartbeats_1771_ = v_initHeartbeats_1683_;
v_maxHeartbeats_1772_ = v_maxHeartbeats_1684_;
v_quotContext_1773_ = v_quotContext_1685_;
v_currMacroScope_1774_ = v_currMacroScope_1686_;
v_cancelTk_x3f_1775_ = v_cancelTk_x3f_1687_;
v_suppressElabErrors_1776_ = v_suppressElabErrors_1688_;
v_inheritedTraceOptions_1777_ = v_inheritedTraceOptions_1689_;
v___y_1778_ = v_a_1652_;
goto v___jp_1764_;
}
}
}
else
{
lean_object* v___x_1810_; 
lean_dec(v_a_1668_);
lean_dec_ref(v___x_1654_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v_a_1656_);
v___x_1810_ = v___x_1670_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1656_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1813_; uint8_t v___y_1815_; uint8_t v___x_1824_; 
lean_dec_ref(v___x_1654_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
v_a_1813_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1813_);
v___x_1824_ = l_Lean_Exception_isInterrupt(v_a_1813_);
if (v___x_1824_ == 0)
{
uint8_t v___x_1825_; 
v___x_1825_ = l_Lean_Exception_isRuntime(v_a_1813_);
v___y_1815_ = v___x_1825_;
goto v___jp_1814_;
}
else
{
lean_dec(v_a_1813_);
v___y_1815_ = v___x_1824_;
goto v___jp_1814_;
}
v___jp_1814_:
{
if (v___y_1815_ == 0)
{
lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v___x_1667_, 0);
lean_dec(v_unused_1823_);
v___x_1817_ = v___x_1667_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_dec(v___x_1667_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 0);
lean_ctor_set(v___x_1817_, 0, v_a_1656_);
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1656_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
else
{
lean_dec(v_a_1656_);
return v___x_1667_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1654_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___boxed(lean_object* v_type_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Compiler_LCNF_toLCNFType(v_type_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1835_, v_x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___boxed(lean_object* v_00_u03b2_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(v_00_u03b2_1838_, v_x_1839_, v_x_1840_);
lean_dec(v_x_1840_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(lean_object* v_00_u03b2_1842_, lean_object* v_m_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___boxed(lean_object* v_00_u03b2_1845_, lean_object* v_m_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(v_00_u03b2_1845_, v_m_1846_);
lean_dec_ref(v_m_1846_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(lean_object* v_00_u03b2_1848_, lean_object* v_x_1849_, size_t v_x_1850_, lean_object* v_x_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1849_, v_x_1850_, v_x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
size_t v_x_20832__boxed_1857_; lean_object* v_res_1858_; 
v_x_20832__boxed_1857_ = lean_unbox_usize(v_x_1855_);
lean_dec(v_x_1855_);
v_res_1858_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(v_00_u03b2_1853_, v_x_1854_, v_x_20832__boxed_1857_, v_x_1856_);
lean_dec(v_x_1856_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(lean_object* v_00_u03c3_1859_, lean_object* v_00_u03b2_1860_, lean_object* v_map_1861_, lean_object* v_f_1862_, lean_object* v_init_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_1861_, v_f_1862_, v_init_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1865_, lean_object* v_00_u03b2_1866_, lean_object* v_map_1867_, lean_object* v_f_1868_, lean_object* v_init_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(v_00_u03c3_1865_, v_00_u03b2_1866_, v_map_1867_, v_f_1868_, v_init_1869_);
lean_dec_ref(v_map_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1871_, lean_object* v_keys_1872_, lean_object* v_vals_1873_, lean_object* v_heq_1874_, lean_object* v_i_1875_, lean_object* v_k_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_keys_1872_, v_vals_1873_, v_i_1875_, v_k_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1878_, lean_object* v_keys_1879_, lean_object* v_vals_1880_, lean_object* v_heq_1881_, lean_object* v_i_1882_, lean_object* v_k_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(v_00_u03b2_1878_, v_keys_1879_, v_vals_1880_, v_heq_1881_, v_i_1882_, v_k_1883_);
lean_dec(v_k_1883_);
lean_dec_ref(v_vals_1880_);
lean_dec_ref(v_keys_1879_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(lean_object* v_map_1885_, lean_object* v_f_1886_, lean_object* v_init_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1886_, v_map_1885_, v_init_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_map_1889_, lean_object* v_f_1890_, lean_object* v_init_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(v_map_1889_, v_f_1890_, v_init_1891_);
lean_dec_ref(v_map_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(lean_object* v_00_u03c3_1893_, lean_object* v_00_u03b2_1894_, lean_object* v_map_1895_, lean_object* v_f_1896_, lean_object* v_init_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1896_, v_map_1895_, v_init_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03c3_1899_, lean_object* v_00_u03b2_1900_, lean_object* v_map_1901_, lean_object* v_f_1902_, lean_object* v_init_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(v_00_u03c3_1899_, v_00_u03b2_1900_, v_map_1901_, v_f_1902_, v_init_1903_);
lean_dec_ref(v_map_1901_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(lean_object* v_00_u03c3_1905_, lean_object* v_00_u03b1_1906_, lean_object* v_00_u03b2_1907_, lean_object* v_f_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1908_, v_x_1909_, v_x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03c3_1912_, lean_object* v_00_u03b1_1913_, lean_object* v_00_u03b2_1914_, lean_object* v_f_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(v_00_u03c3_1912_, v_00_u03b1_1913_, v_00_u03b2_1914_, v_f_1915_, v_x_1916_, v_x_1917_);
lean_dec_ref(v_x_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(lean_object* v_00_u03b1_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_00_u03c3_1921_, lean_object* v_f_1922_, lean_object* v_as_1923_, size_t v_i_1924_, size_t v_stop_1925_, lean_object* v_b_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1922_, v_as_1923_, v_i_1924_, v_stop_1925_, v_b_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___boxed(lean_object* v_00_u03b1_1928_, lean_object* v_00_u03b2_1929_, lean_object* v_00_u03c3_1930_, lean_object* v_f_1931_, lean_object* v_as_1932_, lean_object* v_i_1933_, lean_object* v_stop_1934_, lean_object* v_b_1935_){
_start:
{
size_t v_i_boxed_1936_; size_t v_stop_boxed_1937_; lean_object* v_res_1938_; 
v_i_boxed_1936_ = lean_unbox_usize(v_i_1933_);
lean_dec(v_i_1933_);
v_stop_boxed_1937_ = lean_unbox_usize(v_stop_1934_);
lean_dec(v_stop_1934_);
v_res_1938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(v_00_u03b1_1928_, v_00_u03b2_1929_, v_00_u03c3_1930_, v_f_1931_, v_as_1932_, v_i_boxed_1936_, v_stop_boxed_1937_, v_b_1935_);
lean_dec_ref(v_as_1932_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(lean_object* v_00_u03c3_1939_, lean_object* v_00_u03b1_1940_, lean_object* v_00_u03b2_1941_, lean_object* v_f_1942_, lean_object* v_keys_1943_, lean_object* v_vals_1944_, lean_object* v_heq_1945_, lean_object* v_i_1946_, lean_object* v_acc_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1942_, v_keys_1943_, v_vals_1944_, v_i_1946_, v_acc_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___boxed(lean_object* v_00_u03c3_1949_, lean_object* v_00_u03b1_1950_, lean_object* v_00_u03b2_1951_, lean_object* v_f_1952_, lean_object* v_keys_1953_, lean_object* v_vals_1954_, lean_object* v_heq_1955_, lean_object* v_i_1956_, lean_object* v_acc_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(v_00_u03c3_1949_, v_00_u03b1_1950_, v_00_u03b2_1951_, v_f_1952_, v_keys_1953_, v_vals_1954_, v_heq_1955_, v_i_1956_, v_acc_1957_);
lean_dec_ref(v_vals_1954_);
lean_dec_ref(v_keys_1953_);
return v_res_1958_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f(lean_object* v_a_1963_, lean_object* v_b_1964_){
_start:
{
lean_object* v___y_1968_; uint8_t v___y_1971_; uint8_t v___x_2044_; 
v___x_2044_ = l_Lean_Expr_isErased(v_a_1963_);
if (v___x_2044_ == 0)
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Lean_Expr_isErased(v_b_1964_);
v___y_1971_ = v___x_2045_;
goto v___jp_1970_;
}
else
{
v___y_1971_ = v___x_2044_;
goto v___jp_1970_;
}
v___jp_1965_:
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1966_;
}
v___jp_1967_:
{
if (lean_obj_tag(v___y_1968_) == 0)
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1969_;
}
else
{
return v___y_1968_;
}
}
v___jp_1970_:
{
if (v___y_1971_ == 0)
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_expr_eqv(v_a_1963_, v_b_1964_);
if (v___x_1972_ == 0)
{
lean_object* v_a_x27_1973_; lean_object* v_b_x27_1974_; uint8_t v___x_1975_; 
lean_inc_ref(v_a_1963_);
v_a_x27_1973_ = l_Lean_Expr_headBeta(v_a_1963_);
lean_inc_ref(v_b_1964_);
v_b_x27_1974_ = l_Lean_Expr_headBeta(v_b_1964_);
v___x_1975_ = lean_expr_eqv(v_a_1963_, v_a_x27_1973_);
if (v___x_1975_ == 0)
{
lean_dec_ref(v_b_1964_);
lean_dec_ref(v_a_1963_);
v_a_1963_ = v_a_x27_1973_;
v_b_1964_ = v_b_x27_1974_;
goto _start;
}
else
{
if (v___x_1972_ == 0)
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_expr_eqv(v_b_1964_, v_b_x27_1974_);
if (v___x_1977_ == 0)
{
lean_dec_ref(v_b_1964_);
lean_dec_ref(v_a_1963_);
v_a_1963_ = v_a_x27_1973_;
v_b_1964_ = v_b_x27_1974_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_1974_);
lean_dec_ref(v_a_x27_1973_);
switch(lean_obj_tag(v_a_1963_))
{
case 10:
{
lean_object* v_expr_1979_; 
v_expr_1979_ = lean_ctor_get(v_a_1963_, 1);
lean_inc_ref(v_expr_1979_);
lean_dec_ref(v_a_1963_);
v_a_1963_ = v_expr_1979_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_1964_))
{
case 10:
{
lean_object* v_expr_1981_; 
v_expr_1981_ = lean_ctor_get(v_b_1964_, 1);
lean_inc_ref(v_expr_1981_);
lean_dec_ref(v_b_1964_);
v_b_1964_ = v_expr_1981_;
goto _start;
}
case 5:
{
lean_object* v_fn_1983_; lean_object* v_arg_1984_; lean_object* v_fn_1985_; lean_object* v_arg_1986_; lean_object* v___x_1987_; 
v_fn_1983_ = lean_ctor_get(v_a_1963_, 0);
lean_inc_ref(v_fn_1983_);
v_arg_1984_ = lean_ctor_get(v_a_1963_, 1);
lean_inc_ref(v_arg_1984_);
lean_dec_ref(v_a_1963_);
v_fn_1985_ = lean_ctor_get(v_b_1964_, 0);
lean_inc_ref(v_fn_1985_);
v_arg_1986_ = lean_ctor_get(v_b_1964_, 1);
lean_inc_ref(v_arg_1986_);
lean_dec_ref(v_b_1964_);
v___x_1987_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_fn_1983_, v_fn_1985_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_dec_ref(v_arg_1986_);
lean_dec_ref(v_arg_1984_);
v___y_1968_ = v___x_1987_;
goto v___jp_1967_;
}
else
{
lean_object* v_val_1988_; lean_object* v___x_1989_; 
v_val_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_val_1988_);
lean_dec_ref(v___x_1987_);
v___x_1989_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_arg_1984_, v_arg_1986_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_dec(v_val_1988_);
v___y_1968_ = v___x_1989_;
goto v___jp_1967_;
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1998_; 
v_val_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_val_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = l_Lean_Expr_app___override(v_val_1988_, v_val_1990_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1994_);
v___x_1996_ = v___x_1992_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
default: 
{
lean_dec_ref(v_a_1963_);
lean_dec_ref(v_b_1964_);
goto v___jp_1965_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_1964_))
{
case 10:
{
lean_object* v_expr_1999_; 
v_expr_1999_ = lean_ctor_get(v_b_1964_, 1);
lean_inc_ref(v_expr_1999_);
lean_dec_ref(v_b_1964_);
v_b_1964_ = v_expr_1999_;
goto _start;
}
case 7:
{
lean_object* v_binderName_2001_; lean_object* v_binderType_2002_; lean_object* v_body_2003_; lean_object* v_binderType_2004_; lean_object* v_body_2005_; lean_object* v___x_2006_; 
v_binderName_2001_ = lean_ctor_get(v_a_1963_, 0);
lean_inc(v_binderName_2001_);
v_binderType_2002_ = lean_ctor_get(v_a_1963_, 1);
lean_inc_ref(v_binderType_2002_);
v_body_2003_ = lean_ctor_get(v_a_1963_, 2);
lean_inc_ref(v_body_2003_);
lean_dec_ref(v_a_1963_);
v_binderType_2004_ = lean_ctor_get(v_b_1964_, 1);
lean_inc_ref(v_binderType_2004_);
v_body_2005_ = lean_ctor_get(v_b_1964_, 2);
lean_inc_ref(v_body_2005_);
lean_dec_ref(v_b_1964_);
v___x_2006_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_2002_, v_binderType_2004_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_dec_ref(v_body_2005_);
lean_dec_ref(v_body_2003_);
lean_dec(v_binderName_2001_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_2007_;
}
else
{
return v___x_2006_;
}
}
else
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2018_; 
v_val_2008_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2010_ = v___x_2006_;
v_isShared_2011_ = v_isSharedCheck_2018_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v___x_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2018_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2012_ = l_Lean_Compiler_LCNF_joinTypes(v_body_2003_, v_body_2005_);
v___x_2013_ = 0;
v___x_2014_ = l_Lean_Expr_forallE___override(v_binderName_2001_, v_val_2008_, v___x_2012_, v___x_2013_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2014_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
default: 
{
lean_dec_ref(v_a_1963_);
lean_dec_ref(v_b_1964_);
goto v___jp_1965_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_1964_))
{
case 10:
{
lean_object* v_expr_2019_; 
v_expr_2019_ = lean_ctor_get(v_b_1964_, 1);
lean_inc_ref(v_expr_2019_);
lean_dec_ref(v_b_1964_);
v_b_1964_ = v_expr_2019_;
goto _start;
}
case 6:
{
lean_object* v_binderName_2021_; lean_object* v_binderType_2022_; lean_object* v_body_2023_; lean_object* v_binderType_2024_; lean_object* v_body_2025_; lean_object* v___x_2026_; 
v_binderName_2021_ = lean_ctor_get(v_a_1963_, 0);
lean_inc(v_binderName_2021_);
v_binderType_2022_ = lean_ctor_get(v_a_1963_, 1);
lean_inc_ref(v_binderType_2022_);
v_body_2023_ = lean_ctor_get(v_a_1963_, 2);
lean_inc_ref(v_body_2023_);
lean_dec_ref(v_a_1963_);
v_binderType_2024_ = lean_ctor_get(v_b_1964_, 1);
lean_inc_ref(v_binderType_2024_);
v_body_2025_ = lean_ctor_get(v_b_1964_, 2);
lean_inc_ref(v_body_2025_);
lean_dec_ref(v_b_1964_);
v___x_2026_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_2022_, v_binderType_2024_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_dec_ref(v_body_2025_);
lean_dec_ref(v_body_2023_);
lean_dec(v_binderName_2021_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_2027_;
}
else
{
return v___x_2026_;
}
}
else
{
lean_object* v_val_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2038_; 
v_val_2028_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_val_2028_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2032_ = l_Lean_Compiler_LCNF_joinTypes(v_body_2023_, v_body_2025_);
v___x_2033_ = 0;
v___x_2034_ = l_Lean_Expr_lam___override(v_binderName_2021_, v_val_2028_, v___x_2032_, v___x_2033_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2034_);
v___x_2036_ = v___x_2030_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
default: 
{
lean_dec_ref(v_a_1963_);
lean_dec_ref(v_b_1964_);
goto v___jp_1965_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_1964_) == 10)
{
lean_object* v_expr_2039_; 
v_expr_2039_ = lean_ctor_get(v_b_1964_, 1);
lean_inc_ref(v_expr_2039_);
lean_dec_ref(v_b_1964_);
v_b_1964_ = v_expr_2039_;
goto _start;
}
else
{
lean_dec_ref(v_b_1964_);
lean_dec_ref(v_a_1963_);
goto v___jp_1965_;
}
}
}
}
}
else
{
lean_dec_ref(v_b_1964_);
lean_dec_ref(v_a_1963_);
v_a_1963_ = v_a_x27_1973_;
v_b_1964_ = v_b_x27_1974_;
goto _start;
}
}
}
else
{
lean_object* v___x_2042_; 
lean_dec_ref(v_b_1964_);
v___x_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_a_1963_);
return v___x_2042_;
}
}
else
{
lean_object* v___x_2043_; 
lean_dec_ref(v_b_1964_);
lean_dec_ref(v_a_1963_);
v___x_2043_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1);
return v___x_2043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object* v_a_2046_, lean_object* v_b_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_a_2046_, v_b_2047_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
return v___x_2049_;
}
else
{
lean_object* v_val_2050_; 
v_val_2050_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_val_2050_);
lean_dec_ref(v___x_2048_);
return v_val_2050_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object* v_type_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Expr_headBeta(v_type_2051_);
switch(lean_obj_tag(v___x_2052_))
{
case 3:
{
uint8_t v___x_2053_; 
lean_dec_ref(v___x_2052_);
v___x_2053_ = 1;
return v___x_2053_;
}
case 7:
{
lean_object* v_body_2054_; 
v_body_2054_ = lean_ctor_get(v___x_2052_, 2);
lean_inc_ref(v_body_2054_);
lean_dec_ref(v___x_2052_);
v_type_2051_ = v_body_2054_;
goto _start;
}
default: 
{
uint8_t v___x_2056_; 
lean_dec_ref(v___x_2052_);
v___x_2056_ = 0;
return v___x_2056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTypeFormerType___boxed(lean_object* v_type_2057_){
_start:
{
uint8_t v_res_2058_; lean_object* v_r_2059_; 
v_res_2058_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_2057_);
v_r_2059_ = lean_box(v_res_2058_);
return v_r_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(lean_object* v_msgData_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___x_2064_; lean_object* v_env_2065_; lean_object* v_options_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2064_ = lean_st_ref_get(v___y_2062_);
v_env_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc_ref(v_env_2065_);
lean_dec(v___x_2064_);
v_options_2066_ = lean_ctor_get(v___y_2061_, 2);
v___x_2067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_2068_ = lean_unsigned_to_nat(32u);
v___x_2069_ = lean_mk_empty_array_with_capacity(v___x_2068_);
lean_dec_ref(v___x_2069_);
v___x_2070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_2066_);
v___x_2071_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2071_, 0, v_env_2065_);
lean_ctor_set(v___x_2071_, 1, v___x_2067_);
lean_ctor_set(v___x_2071_, 2, v___x_2070_);
lean_ctor_set(v___x_2071_, 3, v_options_2066_);
v___x_2072_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v_msgData_2060_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0___boxed(lean_object* v_msgData_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msgData_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(lean_object* v_msg_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_ref_2083_; lean_object* v___x_2084_; lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2093_; 
v_ref_2083_ = lean_ctor_get(v___y_2080_, 5);
v___x_2084_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msg_2079_, v___y_2080_, v___y_2081_);
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2093_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2093_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
lean_inc(v_ref_2083_);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v_ref_2083_);
lean_ctor_set(v___x_2089_, 1, v_a_2085_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 1);
lean_ctor_set(v___x_2087_, 0, v___x_2089_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg___boxed(lean_object* v_msg_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2098_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0));
v___x_2101_ = l_Lean_stringToMessageData(v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(lean_object* v_ps_2102_, lean_object* v_i_2103_, lean_object* v_type_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = lean_array_get_size(v_ps_2102_);
v___x_2109_ = lean_nat_dec_lt(v_i_2103_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec(v_i_2103_);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_type_2104_);
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Expr_headBeta(v_type_2104_);
if (lean_obj_tag(v___x_2111_) == 7)
{
lean_object* v_body_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_body_2112_ = lean_ctor_get(v___x_2111_, 2);
lean_inc_ref(v_body_2112_);
lean_dec_ref(v___x_2111_);
v___x_2113_ = lean_unsigned_to_nat(1u);
v___x_2114_ = lean_nat_add(v_i_2103_, v___x_2113_);
v___x_2115_ = lean_array_fget_borrowed(v_ps_2102_, v_i_2103_);
lean_dec(v_i_2103_);
v___x_2116_ = lean_expr_instantiate1(v_body_2112_, v___x_2115_);
lean_dec_ref(v_body_2112_);
v_i_2103_ = v___x_2114_;
v_type_2104_ = v___x_2116_;
goto _start;
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec_ref(v___x_2111_);
lean_dec(v_i_2103_);
v___x_2118_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1);
v___x_2119_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v___x_2118_, v_a_2105_, v_a_2106_);
return v___x_2119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object* v_ps_2120_, lean_object* v_i_2121_, lean_object* v_type_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2120_, v_i_2121_, v_type_2122_, v_a_2123_, v_a_2124_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_ps_2120_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(lean_object* v_00_u03b1_2127_, lean_object* v_msg_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2128_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___boxed(lean_object* v_00_u03b1_2133_, lean_object* v_msg_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(v_00_u03b1_2133_, v_msg_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter___redArg(lean_object* v_e_2139_, lean_object* v_h__1_2140_, lean_object* v_h__2_2141_){
_start:
{
if (lean_obj_tag(v_e_2139_) == 7)
{
lean_object* v_binderName_2142_; lean_object* v_binderType_2143_; lean_object* v_body_2144_; uint8_t v_binderInfo_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec(v_h__2_2141_);
v_binderName_2142_ = lean_ctor_get(v_e_2139_, 0);
lean_inc(v_binderName_2142_);
v_binderType_2143_ = lean_ctor_get(v_e_2139_, 1);
lean_inc_ref(v_binderType_2143_);
v_body_2144_ = lean_ctor_get(v_e_2139_, 2);
lean_inc_ref(v_body_2144_);
v_binderInfo_2145_ = lean_ctor_get_uint8(v_e_2139_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2139_);
v___x_2146_ = lean_box(v_binderInfo_2145_);
v___x_2147_ = lean_apply_4(v_h__1_2140_, v_binderName_2142_, v_binderType_2143_, v_body_2144_, v___x_2146_);
return v___x_2147_;
}
else
{
lean_object* v___x_2148_; 
lean_dec(v_h__1_2140_);
v___x_2148_ = lean_apply_2(v_h__2_2141_, v_e_2139_, lean_box(0));
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter(lean_object* v_motive_2149_, lean_object* v_e_2150_, lean_object* v_h__1_2151_, lean_object* v_h__2_2152_){
_start:
{
if (lean_obj_tag(v_e_2150_) == 7)
{
lean_object* v_binderName_2153_; lean_object* v_binderType_2154_; lean_object* v_body_2155_; uint8_t v_binderInfo_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec(v_h__2_2152_);
v_binderName_2153_ = lean_ctor_get(v_e_2150_, 0);
lean_inc(v_binderName_2153_);
v_binderType_2154_ = lean_ctor_get(v_e_2150_, 1);
lean_inc_ref(v_binderType_2154_);
v_body_2155_ = lean_ctor_get(v_e_2150_, 2);
lean_inc_ref(v_body_2155_);
v_binderInfo_2156_ = lean_ctor_get_uint8(v_e_2150_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2150_);
v___x_2157_ = lean_box(v_binderInfo_2156_);
v___x_2158_ = lean_apply_4(v_h__1_2151_, v_binderName_2153_, v_binderType_2154_, v_body_2155_, v___x_2157_);
return v___x_2158_;
}
else
{
lean_object* v___x_2159_; 
lean_dec(v_h__1_2151_);
v___x_2159_ = lean_apply_2(v_h__2_2152_, v_e_2150_, lean_box(0));
return v___x_2159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object* v_type_2160_, lean_object* v_ps_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2161_, v___x_2165_, v_type_2160_, v_a_2162_, v_a_2163_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object* v_type_2167_, lean_object* v_ps_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_2167_, v_ps_2168_, v_a_2169_, v_a_2170_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec_ref(v_ps_2168_);
return v_res_2172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object* v_type_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_Expr_headBeta(v_type_2173_);
switch(lean_obj_tag(v___x_2174_))
{
case 3:
{
lean_object* v_u_2175_; 
v_u_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_u_2175_);
lean_dec_ref(v___x_2174_);
if (lean_obj_tag(v_u_2175_) == 0)
{
uint8_t v___x_2176_; 
v___x_2176_ = 1;
return v___x_2176_;
}
else
{
uint8_t v___x_2177_; 
lean_dec(v_u_2175_);
v___x_2177_ = 0;
return v___x_2177_;
}
}
case 7:
{
lean_object* v_body_2178_; 
v_body_2178_ = lean_ctor_get(v___x_2174_, 2);
lean_inc_ref(v_body_2178_);
lean_dec_ref(v___x_2174_);
v_type_2173_ = v_body_2178_;
goto _start;
}
default: 
{
uint8_t v___x_2180_; 
lean_dec_ref(v___x_2174_);
v___x_2180_ = 0;
return v___x_2180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPredicateType___boxed(lean_object* v_type_2181_){
_start:
{
uint8_t v_res_2182_; lean_object* v_r_2183_; 
v_res_2182_ = l_Lean_Compiler_LCNF_isPredicateType(v_type_2181_);
v_r_2183_ = lean_box(v_res_2182_);
return v_r_2183_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_maybeTypeFormerType(lean_object* v_type_2184_){
_start:
{
lean_object* v___x_2185_; 
lean_inc_ref(v_type_2184_);
v___x_2185_ = l_Lean_Expr_headBeta(v_type_2184_);
switch(lean_obj_tag(v___x_2185_))
{
case 3:
{
uint8_t v___x_2186_; 
lean_dec_ref(v___x_2185_);
lean_dec_ref(v_type_2184_);
v___x_2186_ = 1;
return v___x_2186_;
}
case 7:
{
lean_object* v_body_2187_; 
lean_dec_ref(v_type_2184_);
v_body_2187_ = lean_ctor_get(v___x_2185_, 2);
lean_inc_ref(v_body_2187_);
lean_dec_ref(v___x_2185_);
v_type_2184_ = v_body_2187_;
goto _start;
}
default: 
{
uint8_t v___x_2189_; 
lean_dec_ref(v___x_2185_);
v___x_2189_ = l_Lean_Expr_isErased(v_type_2184_);
lean_dec_ref(v_type_2184_);
return v___x_2189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_maybeTypeFormerType___boxed(lean_object* v_type_2190_){
_start:
{
uint8_t v_res_2191_; lean_object* v_r_2192_; 
v_res_2191_ = l_Lean_Compiler_LCNF_maybeTypeFormerType(v_type_2190_);
v_r_2192_ = lean_box(v_res_2191_);
return v_r_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object* v_type_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Expr_getAppFn(v_type_2193_);
if (lean_obj_tag(v___x_2196_) == 4)
{
lean_object* v_declName_2197_; lean_object* v___x_2198_; lean_object* v_env_2199_; uint8_t v___x_2200_; 
v_declName_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_declName_2197_);
lean_dec_ref(v___x_2196_);
v___x_2198_ = lean_st_ref_get(v_a_2194_);
v_env_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc_ref(v_env_2199_);
lean_dec(v___x_2198_);
lean_inc(v_declName_2197_);
v___x_2200_ = lean_is_class(v_env_2199_, v_declName_2197_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v_declName_2197_);
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v_declName_2197_);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v___x_2196_);
v___x_2205_ = lean_box(0);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg___boxed(lean_object* v_type_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2207_, v_a_2208_);
lean_dec(v_a_2208_);
lean_dec_ref(v_type_2207_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object* v_type_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2211_, v_a_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___boxed(lean_object* v_type_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Compiler_LCNF_isClass_x3f(v_type_2216_, v_a_2217_, v_a_2218_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec_ref(v_type_2216_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object* v_type_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v___x_2224_; 
lean_inc_ref(v_type_2221_);
v___x_2224_ = l_Lean_Expr_headBeta(v_type_2221_);
if (lean_obj_tag(v___x_2224_) == 7)
{
lean_object* v_body_2225_; 
lean_dec_ref(v_type_2221_);
v_body_2225_ = lean_ctor_get(v___x_2224_, 2);
lean_inc_ref(v_body_2225_);
lean_dec_ref(v___x_2224_);
v_type_2221_ = v_body_2225_;
goto _start;
}
else
{
lean_object* v___x_2227_; 
lean_dec_ref(v___x_2224_);
v___x_2227_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2221_, v_a_2222_);
lean_dec_ref(v_type_2221_);
return v___x_2227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg___boxed(lean_object* v_type_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2228_, v_a_2229_);
lean_dec(v_a_2229_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object* v_type_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2232_, v_a_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___boxed(lean_object* v_type_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Compiler_LCNF_isArrowClass_x3f(v_type_2237_, v_a_2238_, v_a_2239_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object* v_e_2242_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_Expr_headBeta(v_e_2242_);
if (lean_obj_tag(v___x_2243_) == 7)
{
lean_object* v_body_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_body_2244_ = lean_ctor_get(v___x_2243_, 2);
lean_inc_ref(v_body_2244_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = l_Lean_Compiler_LCNF_getArrowArity(v_body_2244_);
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = lean_nat_add(v___x_2245_, v___x_2246_);
lean_dec(v___x_2245_);
return v___x_2247_;
}
else
{
lean_object* v___x_2248_; 
lean_dec_ref(v___x_2243_);
v___x_2248_ = lean_unsigned_to_nat(0u);
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object* v_type_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Expr_getAppFn(v_type_2249_);
if (lean_obj_tag(v___x_2256_) == 4)
{
lean_object* v_declName_2257_; lean_object* v___x_2258_; lean_object* v_env_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; 
v_declName_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_declName_2257_);
lean_dec_ref(v___x_2256_);
v___x_2258_ = lean_st_ref_get(v_a_2250_);
v_env_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc_ref(v_env_2259_);
lean_dec(v___x_2258_);
v___x_2260_ = 0;
v___x_2261_ = l_Lean_Environment_find_x3f(v_env_2259_, v_declName_2257_, v___x_2260_);
if (lean_obj_tag(v___x_2261_) == 1)
{
lean_object* v_val_2262_; 
v_val_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_val_2262_);
lean_dec_ref(v___x_2261_);
if (lean_obj_tag(v_val_2262_) == 5)
{
lean_object* v_val_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2274_; 
v_val_2263_ = lean_ctor_get(v_val_2262_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_val_2262_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2265_ = v_val_2262_;
v_isShared_2266_ = v_isSharedCheck_2274_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_val_2263_);
lean_dec(v_val_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2274_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2267_ = l_Lean_InductiveVal_numCtors(v_val_2263_);
lean_dec_ref(v_val_2263_);
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = lean_nat_dec_eq(v___x_2267_, v___x_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(v___x_2269_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set_tag(v___x_2265_, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2270_);
v___x_2272_ = v___x_2265_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
else
{
lean_dec(v_val_2262_);
goto v___jp_2252_;
}
}
else
{
lean_dec(v___x_2261_);
goto v___jp_2252_;
}
}
else
{
uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec_ref(v___x_2256_);
v___x_2275_ = 0;
v___x_2276_ = lean_box(v___x_2275_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
v___jp_2252_:
{
uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = 0;
v___x_2254_ = lean_box(v___x_2253_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg___boxed(lean_object* v_type_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2278_, v_a_2279_);
lean_dec(v_a_2279_);
lean_dec_ref(v_type_2278_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object* v_type_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2282_, v_a_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___boxed(lean_object* v_type_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors(v_type_2287_, v_a_2288_, v_a_2289_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec_ref(v_type_2287_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object* v_n_2293_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2295_ = l_Lean_Name_str___override(v_n_2293_, v___x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isBoxedName(lean_object* v_name_2296_){
_start:
{
if (lean_obj_tag(v_name_2296_) == 1)
{
lean_object* v_str_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v_str_2297_ = lean_ctor_get(v_name_2296_, 1);
v___x_2298_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2299_ = lean_string_dec_eq(v_str_2297_, v___x_2298_);
return v___x_2299_;
}
else
{
uint8_t v___x_2300_; 
v___x_2300_ = 0;
return v___x_2300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isBoxedName___boxed(lean_object* v_name_2301_){
_start:
{
uint8_t v_res_2302_; lean_object* v_r_2303_; 
v_res_2302_ = l_Lean_Compiler_LCNF_isBoxedName(v_name_2301_);
lean_dec(v_name_2301_);
v_r_2303_ = lean_box(v_res_2302_);
return v_r_2303_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_box(0);
v___x_2308_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__1));
v___x_2309_ = l_Lean_Expr_const___override(v___x_2308_, v___x_2307_);
return v___x_2309_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float(void){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_box(0);
v___x_2315_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__1));
v___x_2316_ = l_Lean_Expr_const___override(v___x_2315_, v___x_2314_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32(void){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2);
return v___x_2317_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_box(0);
v___x_2322_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1));
v___x_2323_ = l_Lean_Expr_const___override(v___x_2322_, v___x_2321_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8(void){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2);
return v___x_2324_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = lean_box(0);
v___x_2329_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1));
v___x_2330_ = l_Lean_Expr_const___override(v___x_2329_, v___x_2328_);
return v___x_2330_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16(void){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2);
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = lean_box(0);
v___x_2336_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1));
v___x_2337_ = l_Lean_Expr_const___override(v___x_2336_, v___x_2335_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32(void){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2342_ = lean_box(0);
v___x_2343_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1));
v___x_2344_ = l_Lean_Expr_const___override(v___x_2343_, v___x_2342_);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64(void){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2);
return v___x_2345_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2349_ = lean_box(0);
v___x_2350_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__1));
v___x_2351_ = l_Lean_Expr_const___override(v___x_2350_, v___x_2349_);
return v___x_2351_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize(void){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_usize___closed__2, &l_Lean_Compiler_LCNF_ImpureType_usize___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2);
return v___x_2352_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = lean_box(0);
v___x_2354_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_2355_ = l_Lean_Expr_const___override(v___x_2354_, v___x_2353_);
return v___x_2355_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased(void){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_erased___closed__0, &l_Lean_Compiler_LCNF_ImpureType_erased___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0);
return v___x_2356_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = lean_box(0);
v___x_2361_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__1));
v___x_2362_ = l_Lean_Expr_const___override(v___x_2361_, v___x_2360_);
return v___x_2362_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object(void){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2363_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = lean_box(0);
v___x_2368_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1));
v___x_2369_ = l_Lean_Expr_const___override(v___x_2368_, v___x_2367_);
return v___x_2369_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject(void){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = lean_box(0);
v___x_2375_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1));
v___x_2376_ = l_Lean_Expr_const___override(v___x_2375_, v___x_2374_);
return v___x_2376_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged(void){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2377_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_box(0);
v___x_2379_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_2380_ = l_Lean_Expr_const___override(v___x_2379_, v___x_2378_);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void(void){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_void___closed__0, &l_Lean_Compiler_LCNF_ImpureType_void___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0);
return v___x_2381_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object* v_x_2382_){
_start:
{
if (lean_obj_tag(v_x_2382_) == 4)
{
lean_object* v_declName_2383_; 
v_declName_2383_ = lean_ctor_get(v_x_2382_, 0);
if (lean_obj_tag(v_declName_2383_) == 1)
{
lean_object* v_pre_2384_; 
v_pre_2384_ = lean_ctor_get(v_declName_2383_, 0);
if (lean_obj_tag(v_pre_2384_) == 0)
{
lean_object* v_us_2385_; lean_object* v_str_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v_us_2385_ = lean_ctor_get(v_x_2382_, 1);
v_str_2386_ = lean_ctor_get(v_declName_2383_, 1);
v___x_2387_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2388_ = lean_string_dec_eq(v_str_2386_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2390_ = lean_string_dec_eq(v_str_2386_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2392_ = lean_string_dec_eq(v_str_2386_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2394_ = lean_string_dec_eq(v_str_2386_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0));
v___x_2396_ = lean_string_dec_eq(v_str_2386_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2398_ = lean_string_dec_eq(v_str_2386_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__0));
v___x_2400_ = lean_string_dec_eq(v_str_2386_, v___x_2399_);
if (v___x_2400_ == 0)
{
return v___x_2400_;
}
else
{
if (lean_obj_tag(v_us_2385_) == 0)
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
if (lean_obj_tag(v_us_2385_) == 0)
{
return v___x_2398_;
}
else
{
return v___x_2396_;
}
}
}
else
{
if (lean_obj_tag(v_us_2385_) == 0)
{
return v___x_2396_;
}
else
{
return v___x_2394_;
}
}
}
else
{
if (lean_obj_tag(v_us_2385_) == 0)
{
return v___x_2394_;
}
else
{
return v___x_2392_;
}
}
}
else
{
if (lean_obj_tag(v_us_2385_) == 0)
{
return v___x_2392_;
}
else
{
return v___x_2390_;
}
}
}
else
{
if (lean_obj_tag(v_us_2385_) == 0)
{
return v___x_2390_;
}
else
{
return v___x_2388_;
}
}
}
else
{
if (lean_obj_tag(v_us_2385_) == 0)
{
return v___x_2388_;
}
else
{
uint8_t v___x_2401_; 
v___x_2401_ = 0;
return v___x_2401_;
}
}
}
else
{
uint8_t v___x_2402_; 
v___x_2402_ = 0;
return v___x_2402_;
}
}
else
{
uint8_t v___x_2403_; 
v___x_2403_ = 0;
return v___x_2403_;
}
}
else
{
uint8_t v___x_2404_; 
v___x_2404_ = 0;
return v___x_2404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar___boxed(lean_object* v_x_2405_){
_start:
{
uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_res_2406_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_x_2405_);
lean_dec_ref(v_x_2405_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(lean_object* v_x_2408_){
_start:
{
if (lean_obj_tag(v_x_2408_) == 4)
{
lean_object* v_declName_2409_; 
v_declName_2409_ = lean_ctor_get(v_x_2408_, 0);
if (lean_obj_tag(v_declName_2409_) == 1)
{
lean_object* v_pre_2410_; 
v_pre_2410_ = lean_ctor_get(v_declName_2409_, 0);
if (lean_obj_tag(v_pre_2410_) == 0)
{
lean_object* v_us_2411_; lean_object* v_str_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v_us_2411_ = lean_ctor_get(v_x_2408_, 1);
v_str_2412_ = lean_ctor_get(v_declName_2409_, 1);
v___x_2413_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2414_ = lean_string_dec_eq(v_str_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2415_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2416_ = lean_string_dec_eq(v_str_2412_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2418_ = lean_string_dec_eq(v_str_2412_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2420_ = lean_string_dec_eq(v_str_2412_, v___x_2419_);
if (v___x_2420_ == 0)
{
return v___x_2420_;
}
else
{
if (lean_obj_tag(v_us_2411_) == 0)
{
return v___x_2420_;
}
else
{
return v___x_2418_;
}
}
}
else
{
if (lean_obj_tag(v_us_2411_) == 0)
{
return v___x_2418_;
}
else
{
return v___x_2416_;
}
}
}
else
{
if (lean_obj_tag(v_us_2411_) == 0)
{
return v___x_2416_;
}
else
{
return v___x_2414_;
}
}
}
else
{
if (lean_obj_tag(v_us_2411_) == 0)
{
return v___x_2414_;
}
else
{
uint8_t v___x_2421_; 
v___x_2421_ = 0;
return v___x_2421_;
}
}
}
else
{
uint8_t v___x_2422_; 
v___x_2422_ = 0;
return v___x_2422_;
}
}
else
{
uint8_t v___x_2423_; 
v___x_2423_ = 0;
return v___x_2423_;
}
}
else
{
uint8_t v___x_2424_; 
v___x_2424_ = 0;
return v___x_2424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj___boxed(lean_object* v_x_2425_){
_start:
{
uint8_t v_res_2426_; lean_object* v_r_2427_; 
v_res_2426_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(v_x_2425_);
lean_dec_ref(v_x_2425_);
v_r_2427_ = lean_box(v_res_2426_);
return v_r_2427_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object* v_x_2428_){
_start:
{
if (lean_obj_tag(v_x_2428_) == 4)
{
lean_object* v_declName_2429_; 
v_declName_2429_ = lean_ctor_get(v_x_2428_, 0);
if (lean_obj_tag(v_declName_2429_) == 1)
{
lean_object* v_pre_2430_; 
v_pre_2430_ = lean_ctor_get(v_declName_2429_, 0);
if (lean_obj_tag(v_pre_2430_) == 0)
{
lean_object* v_us_2431_; lean_object* v_str_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v_us_2431_ = lean_ctor_get(v_x_2428_, 1);
v_str_2432_ = lean_ctor_get(v_declName_2429_, 1);
v___x_2433_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2434_ = lean_string_dec_eq(v_str_2432_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; uint8_t v___x_2436_; 
v___x_2435_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2436_ = lean_string_dec_eq(v_str_2432_, v___x_2435_);
if (v___x_2436_ == 0)
{
return v___x_2436_;
}
else
{
if (lean_obj_tag(v_us_2431_) == 0)
{
return v___x_2436_;
}
else
{
return v___x_2434_;
}
}
}
else
{
if (lean_obj_tag(v_us_2431_) == 0)
{
return v___x_2434_;
}
else
{
uint8_t v___x_2437_; 
v___x_2437_ = 0;
return v___x_2437_;
}
}
}
else
{
uint8_t v___x_2438_; 
v___x_2438_ = 0;
return v___x_2438_;
}
}
else
{
uint8_t v___x_2439_; 
v___x_2439_ = 0;
return v___x_2439_;
}
}
else
{
uint8_t v___x_2440_; 
v___x_2440_ = 0;
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef___boxed(lean_object* v_x_2441_){
_start:
{
uint8_t v_res_2442_; lean_object* v_r_2443_; 
v_res_2442_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_x_2441_);
lean_dec_ref(v_x_2441_);
v_r_2443_ = lean_box(v_res_2442_);
return v_r_2443_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(lean_object* v_x_2444_){
_start:
{
if (lean_obj_tag(v_x_2444_) == 4)
{
lean_object* v_declName_2445_; 
v_declName_2445_ = lean_ctor_get(v_x_2444_, 0);
if (lean_obj_tag(v_declName_2445_) == 1)
{
lean_object* v_pre_2446_; 
v_pre_2446_ = lean_ctor_get(v_declName_2445_, 0);
if (lean_obj_tag(v_pre_2446_) == 0)
{
lean_object* v_us_2447_; lean_object* v_str_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v_us_2447_ = lean_ctor_get(v_x_2444_, 1);
v_str_2448_ = lean_ctor_get(v_declName_2445_, 1);
v___x_2449_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2450_ = lean_string_dec_eq(v_str_2448_, v___x_2449_);
if (v___x_2450_ == 0)
{
return v___x_2450_;
}
else
{
if (lean_obj_tag(v_us_2447_) == 0)
{
return v___x_2450_;
}
else
{
uint8_t v___x_2451_; 
v___x_2451_ = 0;
return v___x_2451_;
}
}
}
else
{
uint8_t v___x_2452_; 
v___x_2452_ = 0;
return v___x_2452_;
}
}
else
{
uint8_t v___x_2453_; 
v___x_2453_ = 0;
return v___x_2453_;
}
}
else
{
uint8_t v___x_2454_; 
v___x_2454_ = 0;
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef___boxed(lean_object* v_x_2455_){
_start:
{
uint8_t v_res_2456_; lean_object* v_r_2457_; 
v_res_2456_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_x_2455_);
lean_dec_ref(v_x_2455_);
v_r_2457_ = lean_box(v_res_2456_);
return v_r_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object* v_x_2458_){
_start:
{
if (lean_obj_tag(v_x_2458_) == 4)
{
lean_object* v_declName_2465_; 
v_declName_2465_ = lean_ctor_get(v_x_2458_, 0);
if (lean_obj_tag(v_declName_2465_) == 1)
{
lean_object* v_pre_2466_; 
v_pre_2466_ = lean_ctor_get(v_declName_2465_, 0);
if (lean_obj_tag(v_pre_2466_) == 0)
{
lean_object* v_us_2467_; lean_object* v_str_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v_us_2467_ = lean_ctor_get(v_x_2458_, 1);
v_str_2468_ = lean_ctor_get(v_declName_2465_, 1);
v___x_2469_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2470_ = lean_string_dec_eq(v_str_2468_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2472_ = lean_string_dec_eq(v_str_2468_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2473_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2474_ = lean_string_dec_eq(v_str_2468_, v___x_2473_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2475_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2476_ = lean_string_dec_eq(v_str_2468_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2477_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2478_ = lean_string_dec_eq(v_str_2468_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2479_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2480_ = lean_string_dec_eq(v_str_2468_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2481_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2482_ = lean_string_dec_eq(v_str_2468_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2483_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2484_ = lean_string_dec_eq(v_str_2468_, v___x_2483_);
if (v___x_2484_ == 0)
{
goto v___jp_2459_;
}
else
{
if (lean_obj_tag(v_us_2467_) == 0)
{
goto v___jp_2463_;
}
else
{
goto v___jp_2459_;
}
}
}
else
{
if (lean_obj_tag(v_us_2467_) == 0)
{
goto v___jp_2463_;
}
else
{
goto v___jp_2459_;
}
}
}
else
{
if (lean_obj_tag(v_us_2467_) == 0)
{
goto v___jp_2463_;
}
else
{
goto v___jp_2459_;
}
}
}
else
{
if (lean_obj_tag(v_us_2467_) == 0)
{
goto v___jp_2463_;
}
else
{
goto v___jp_2459_;
}
}
}
else
{
if (lean_obj_tag(v_us_2467_) == 0)
{
goto v___jp_2461_;
}
else
{
goto v___jp_2459_;
}
}
}
else
{
if (lean_obj_tag(v_us_2467_) == 0)
{
goto v___jp_2461_;
}
else
{
goto v___jp_2459_;
}
}
}
else
{
if (lean_obj_tag(v_us_2467_) == 0)
{
goto v___jp_2461_;
}
else
{
goto v___jp_2459_;
}
}
}
else
{
if (lean_obj_tag(v_us_2467_) == 0)
{
goto v___jp_2461_;
}
else
{
goto v___jp_2459_;
}
}
}
else
{
goto v___jp_2459_;
}
}
else
{
goto v___jp_2459_;
}
}
else
{
goto v___jp_2459_;
}
v___jp_2459_:
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2460_;
}
v___jp_2461_:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2462_;
}
v___jp_2463_:
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed___boxed(lean_object* v_x_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_x_2485_);
lean_dec_ref(v_x_2485_);
return v_res_2486_;
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
