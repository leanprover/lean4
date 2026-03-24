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
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
v___x_116_ = lean_apply_6(v_k_109_, v_b_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, lean_box(0));
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_117_, lean_object* v_b_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(v_k_117_, v_b_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
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
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
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
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed(lean_object* v_xs_194_, lean_object* v_body_195_, lean_object* v_x_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(v_xs_194_, v_body_195_, v_x_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(lean_object* v_type_203_, lean_object* v_xs_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; 
switch(lean_obj_tag(v_type_203_))
{
case 3:
{
lean_object* v_u_242_; 
v_u_242_ = lean_ctor_get(v_type_203_, 0);
if (lean_obj_tag(v_u_242_) == 0)
{
uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v_type_203_);
lean_dec_ref(v_xs_204_);
v___x_243_ = 1;
v___x_244_ = lean_box(v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
else
{
v___y_215_ = v_a_205_;
v___y_216_ = v_a_206_;
v___y_217_ = v_a_207_;
v___y_218_ = v_a_208_;
goto v___jp_214_;
}
}
case 7:
{
lean_object* v_binderName_246_; lean_object* v_binderType_247_; lean_object* v_body_248_; uint8_t v_binderInfo_249_; lean_object* v___f_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; 
v_binderName_246_ = lean_ctor_get(v_type_203_, 0);
lean_inc(v_binderName_246_);
v_binderType_247_ = lean_ctor_get(v_type_203_, 1);
lean_inc_ref(v_binderType_247_);
v_body_248_ = lean_ctor_get(v_type_203_, 2);
lean_inc_ref(v_body_248_);
v_binderInfo_249_ = lean_ctor_get_uint8(v_type_203_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_203_);
lean_inc_ref(v_xs_204_);
v___f_250_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_250_, 0, v_xs_204_);
lean_closure_set(v___f_250_, 1, v_body_248_);
v___x_251_ = lean_expr_instantiate_rev(v_binderType_247_, v_xs_204_);
lean_dec_ref(v_xs_204_);
lean_dec_ref(v_binderType_247_);
v___x_252_ = 0;
v___x_253_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_246_, v_binderInfo_249_, v___x_251_, v___f_250_, v___x_252_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
return v___x_253_;
}
default: 
{
v___y_215_ = v_a_205_;
v___y_216_ = v_a_206_;
v___y_217_ = v_a_207_;
v___y_218_ = v_a_208_;
goto v___jp_214_;
}
}
v___jp_210_:
{
uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = 0;
v___x_212_ = lean_box(v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
v___jp_214_:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_expr_instantiate_rev(v_type_203_, v_xs_204_);
lean_dec_ref(v_xs_204_);
lean_dec_ref(v_type_203_);
v___x_220_ = l_Lean_Meta_whnfD(v___x_219_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_233_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_233_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_233_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_233_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
switch(lean_obj_tag(v_a_221_))
{
case 3:
{
lean_object* v_u_225_; 
v_u_225_ = lean_ctor_get(v_a_221_, 0);
lean_inc(v_u_225_);
lean_dec_ref(v_a_221_);
if (lean_obj_tag(v_u_225_) == 0)
{
uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_226_ = 1;
v___x_227_ = lean_box(v___x_226_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_227_);
v___x_229_ = v___x_223_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
else
{
lean_dec(v_u_225_);
lean_del_object(v___x_223_);
goto v___jp_210_;
}
}
case 7:
{
lean_object* v___x_231_; 
lean_del_object(v___x_223_);
v___x_231_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v_type_203_ = v_a_221_;
v_xs_204_ = v___x_231_;
v_a_205_ = v___y_215_;
v_a_206_ = v___y_216_;
v_a_207_ = v___y_217_;
v_a_208_ = v___y_218_;
goto _start;
}
default: 
{
lean_del_object(v___x_223_);
lean_dec(v_a_221_);
goto v___jp_210_;
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_234_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_220_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_220_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(lean_object* v_xs_254_, lean_object* v_body_255_, lean_object* v_x_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_array_push(v_xs_254_, v_x_256_);
v___x_263_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_body_255_, v___x_262_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___boxed(lean_object* v_type_264_, lean_object* v_xs_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_264_, v_xs_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType(lean_object* v_type_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_type_272_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_280_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(v_type_272_, v___x_279_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref(v_type_272_);
v___x_281_ = lean_box(v___x_278_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormerType___boxed(lean_object* v_type_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Compiler_LCNF_isPropFormerType(v_type_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer(lean_object* v_e_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; 
lean_inc(v_a_294_);
lean_inc_ref(v_a_293_);
lean_inc(v_a_292_);
lean_inc_ref(v_a_291_);
v___x_296_ = lean_infer_type(v_e_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref(v___x_296_);
v___x_298_ = l_Lean_Compiler_LCNF_isPropFormerType(v_a_297_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
return v___x_298_;
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_a_299_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_296_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_296_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPropFormer___boxed(lean_object* v_e_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Compiler_LCNF_isPropFormer(v_e_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
return v_res_313_;
}
}
static uint64_t _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0(void){
_start:
{
uint8_t v___x_314_; uint64_t v___x_315_; 
v___x_314_ = 0;
v___x_315_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(lean_object* v_type_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; uint8_t v_foApprox_323_; uint8_t v_ctxApprox_324_; uint8_t v_quasiPatternApprox_325_; uint8_t v_constApprox_326_; uint8_t v_isDefEqStuckEx_327_; uint8_t v_unificationHints_328_; uint8_t v_proofIrrelevance_329_; uint8_t v_assignSyntheticOpaque_330_; uint8_t v_offsetCnstrs_331_; uint8_t v_etaStruct_332_; uint8_t v_univApprox_333_; uint8_t v_iota_334_; uint8_t v_beta_335_; uint8_t v_proj_336_; uint8_t v_zeta_337_; uint8_t v_zetaDelta_338_; uint8_t v_zetaUnused_339_; uint8_t v_zetaHave_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_371_; 
v___x_322_ = l_Lean_Meta_Context_config(v_a_317_);
v_foApprox_323_ = lean_ctor_get_uint8(v___x_322_, 0);
v_ctxApprox_324_ = lean_ctor_get_uint8(v___x_322_, 1);
v_quasiPatternApprox_325_ = lean_ctor_get_uint8(v___x_322_, 2);
v_constApprox_326_ = lean_ctor_get_uint8(v___x_322_, 3);
v_isDefEqStuckEx_327_ = lean_ctor_get_uint8(v___x_322_, 4);
v_unificationHints_328_ = lean_ctor_get_uint8(v___x_322_, 5);
v_proofIrrelevance_329_ = lean_ctor_get_uint8(v___x_322_, 6);
v_assignSyntheticOpaque_330_ = lean_ctor_get_uint8(v___x_322_, 7);
v_offsetCnstrs_331_ = lean_ctor_get_uint8(v___x_322_, 8);
v_etaStruct_332_ = lean_ctor_get_uint8(v___x_322_, 10);
v_univApprox_333_ = lean_ctor_get_uint8(v___x_322_, 11);
v_iota_334_ = lean_ctor_get_uint8(v___x_322_, 12);
v_beta_335_ = lean_ctor_get_uint8(v___x_322_, 13);
v_proj_336_ = lean_ctor_get_uint8(v___x_322_, 14);
v_zeta_337_ = lean_ctor_get_uint8(v___x_322_, 15);
v_zetaDelta_338_ = lean_ctor_get_uint8(v___x_322_, 16);
v_zetaUnused_339_ = lean_ctor_get_uint8(v___x_322_, 17);
v_zetaHave_340_ = lean_ctor_get_uint8(v___x_322_, 18);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_371_ == 0)
{
v___x_342_ = v___x_322_;
v_isShared_343_ = v_isSharedCheck_371_;
goto v_resetjp_341_;
}
else
{
lean_dec(v___x_322_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_371_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint8_t v_trackZetaDelta_344_; lean_object* v_zetaDeltaSet_345_; lean_object* v_lctx_346_; lean_object* v_localInstances_347_; lean_object* v_defEqCtx_x3f_348_; lean_object* v_synthPendingDepth_349_; lean_object* v_canUnfold_x3f_350_; uint8_t v_univApprox_351_; uint8_t v_inTypeClassResolution_352_; uint8_t v_cacheInferType_353_; uint8_t v___x_354_; lean_object* v_config_356_; 
v_trackZetaDelta_344_ = lean_ctor_get_uint8(v_a_317_, sizeof(void*)*7);
v_zetaDeltaSet_345_ = lean_ctor_get(v_a_317_, 1);
v_lctx_346_ = lean_ctor_get(v_a_317_, 2);
v_localInstances_347_ = lean_ctor_get(v_a_317_, 3);
v_defEqCtx_x3f_348_ = lean_ctor_get(v_a_317_, 4);
v_synthPendingDepth_349_ = lean_ctor_get(v_a_317_, 5);
v_canUnfold_x3f_350_ = lean_ctor_get(v_a_317_, 6);
v_univApprox_351_ = lean_ctor_get_uint8(v_a_317_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_352_ = lean_ctor_get_uint8(v_a_317_, sizeof(void*)*7 + 2);
v_cacheInferType_353_ = lean_ctor_get_uint8(v_a_317_, sizeof(void*)*7 + 3);
v___x_354_ = 0;
if (v_isShared_343_ == 0)
{
v_config_356_ = v___x_342_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 0, v_foApprox_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 1, v_ctxApprox_324_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 2, v_quasiPatternApprox_325_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 3, v_constApprox_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 4, v_isDefEqStuckEx_327_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 5, v_unificationHints_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 6, v_proofIrrelevance_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 7, v_assignSyntheticOpaque_330_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 8, v_offsetCnstrs_331_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 10, v_etaStruct_332_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 11, v_univApprox_333_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 12, v_iota_334_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 13, v_beta_335_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 14, v_proj_336_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 15, v_zeta_337_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 16, v_zetaDelta_338_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 17, v_zetaUnused_339_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, 18, v_zetaHave_340_);
v_config_356_ = v_reuseFailAlloc_370_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
uint64_t v___x_357_; uint64_t v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; uint64_t v___x_361_; uint64_t v_key_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_ctor_set_uint8(v_config_356_, 9, v___x_354_);
v___x_357_ = l_Lean_Meta_Context_configKey(v_a_317_);
v___x_358_ = 2ULL;
v___x_359_ = lean_uint64_shift_right(v___x_357_, v___x_358_);
v___x_360_ = lean_uint64_shift_left(v___x_359_, v___x_358_);
v___x_361_ = lean_uint64_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0);
v_key_362_ = lean_uint64_lor(v___x_360_, v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_363_, 0, v_config_356_);
lean_ctor_set_uint64(v___x_363_, sizeof(void*)*1, v_key_362_);
lean_inc(v_canUnfold_x3f_350_);
lean_inc(v_synthPendingDepth_349_);
lean_inc(v_defEqCtx_x3f_348_);
lean_inc_ref(v_localInstances_347_);
lean_inc_ref(v_lctx_346_);
lean_inc(v_zetaDeltaSet_345_);
v___x_364_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_zetaDeltaSet_345_);
lean_ctor_set(v___x_364_, 2, v_lctx_346_);
lean_ctor_set(v___x_364_, 3, v_localInstances_347_);
lean_ctor_set(v___x_364_, 4, v_defEqCtx_x3f_348_);
lean_ctor_set(v___x_364_, 5, v_synthPendingDepth_349_);
lean_ctor_set(v___x_364_, 6, v_canUnfold_x3f_350_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*7, v_trackZetaDelta_344_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*7 + 1, v_univApprox_351_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*7 + 2, v_inTypeClassResolution_352_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*7 + 3, v_cacheInferType_353_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
v___x_365_ = lean_whnf(v_type_316_, v___x_364_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_inc(v_a_366_);
v___x_367_ = l_Lean_Expr_eta(v_a_366_);
v___x_368_ = lean_expr_eqv(v___x_367_, v_a_366_);
lean_dec(v_a_366_);
if (v___x_368_ == 0)
{
lean_dec_ref(v___x_365_);
v_type_316_ = v___x_367_;
goto _start;
}
else
{
lean_dec_ref(v___x_367_);
return v___x_365_;
}
}
else
{
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___boxed(lean_object* v_type_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(lean_object* v_msgData_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; lean_object* v_env_386_; lean_object* v___x_387_; lean_object* v_mctx_388_; lean_object* v_lctx_389_; lean_object* v_options_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_385_ = lean_st_ref_get(v___y_383_);
v_env_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_env_386_);
lean_dec(v___x_385_);
v___x_387_ = lean_st_ref_get(v___y_381_);
v_mctx_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_mctx_388_);
lean_dec(v___x_387_);
v_lctx_389_ = lean_ctor_get(v___y_380_, 2);
v_options_390_ = lean_ctor_get(v___y_382_, 2);
lean_inc_ref(v_options_390_);
lean_inc_ref(v_lctx_389_);
v___x_391_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_391_, 0, v_env_386_);
lean_ctor_set(v___x_391_, 1, v_mctx_388_);
lean_ctor_set(v___x_391_, 2, v_lctx_389_);
lean_ctor_set(v___x_391_, 3, v_options_390_);
v___x_392_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_msgData_379_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6___boxed(lean_object* v_msgData_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msgData_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_ref_407_; lean_object* v___x_408_; lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_417_; 
v_ref_407_ = lean_ctor_get(v___y_404_, 5);
v___x_408_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_417_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
lean_inc(v_ref_407_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v_ref_407_);
lean_ctor_set(v___x_413_, 1, v_a_409_);
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 1);
lean_ctor_set(v___x_411_, 0, v___x_413_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg___boxed(lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(lean_object* v_ref_425_, lean_object* v_msg_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_fileName_432_; lean_object* v_fileMap_433_; lean_object* v_options_434_; lean_object* v_currRecDepth_435_; lean_object* v_maxRecDepth_436_; lean_object* v_ref_437_; lean_object* v_currNamespace_438_; lean_object* v_openDecls_439_; lean_object* v_initHeartbeats_440_; lean_object* v_maxHeartbeats_441_; lean_object* v_quotContext_442_; lean_object* v_currMacroScope_443_; uint8_t v_diag_444_; lean_object* v_cancelTk_x3f_445_; uint8_t v_suppressElabErrors_446_; lean_object* v_inheritedTraceOptions_447_; lean_object* v_ref_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_fileName_432_ = lean_ctor_get(v___y_429_, 0);
v_fileMap_433_ = lean_ctor_get(v___y_429_, 1);
v_options_434_ = lean_ctor_get(v___y_429_, 2);
v_currRecDepth_435_ = lean_ctor_get(v___y_429_, 3);
v_maxRecDepth_436_ = lean_ctor_get(v___y_429_, 4);
v_ref_437_ = lean_ctor_get(v___y_429_, 5);
v_currNamespace_438_ = lean_ctor_get(v___y_429_, 6);
v_openDecls_439_ = lean_ctor_get(v___y_429_, 7);
v_initHeartbeats_440_ = lean_ctor_get(v___y_429_, 8);
v_maxHeartbeats_441_ = lean_ctor_get(v___y_429_, 9);
v_quotContext_442_ = lean_ctor_get(v___y_429_, 10);
v_currMacroScope_443_ = lean_ctor_get(v___y_429_, 11);
v_diag_444_ = lean_ctor_get_uint8(v___y_429_, sizeof(void*)*14);
v_cancelTk_x3f_445_ = lean_ctor_get(v___y_429_, 12);
v_suppressElabErrors_446_ = lean_ctor_get_uint8(v___y_429_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_447_ = lean_ctor_get(v___y_429_, 13);
v_ref_448_ = l_Lean_replaceRef(v_ref_425_, v_ref_437_);
lean_inc_ref(v_inheritedTraceOptions_447_);
lean_inc(v_cancelTk_x3f_445_);
lean_inc(v_currMacroScope_443_);
lean_inc(v_quotContext_442_);
lean_inc(v_maxHeartbeats_441_);
lean_inc(v_initHeartbeats_440_);
lean_inc(v_openDecls_439_);
lean_inc(v_currNamespace_438_);
lean_inc(v_maxRecDepth_436_);
lean_inc(v_currRecDepth_435_);
lean_inc_ref(v_options_434_);
lean_inc_ref(v_fileMap_433_);
lean_inc_ref(v_fileName_432_);
v___x_449_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_449_, 0, v_fileName_432_);
lean_ctor_set(v___x_449_, 1, v_fileMap_433_);
lean_ctor_set(v___x_449_, 2, v_options_434_);
lean_ctor_set(v___x_449_, 3, v_currRecDepth_435_);
lean_ctor_set(v___x_449_, 4, v_maxRecDepth_436_);
lean_ctor_set(v___x_449_, 5, v_ref_448_);
lean_ctor_set(v___x_449_, 6, v_currNamespace_438_);
lean_ctor_set(v___x_449_, 7, v_openDecls_439_);
lean_ctor_set(v___x_449_, 8, v_initHeartbeats_440_);
lean_ctor_set(v___x_449_, 9, v_maxHeartbeats_441_);
lean_ctor_set(v___x_449_, 10, v_quotContext_442_);
lean_ctor_set(v___x_449_, 11, v_currMacroScope_443_);
lean_ctor_set(v___x_449_, 12, v_cancelTk_x3f_445_);
lean_ctor_set(v___x_449_, 13, v_inheritedTraceOptions_447_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*14, v_diag_444_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*14 + 1, v_suppressElabErrors_446_);
v___x_450_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_426_, v___y_427_, v___y_428_, v___x_449_, v___y_430_);
lean_dec_ref(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg___boxed(lean_object* v_ref_451_, lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_451_, v_msg_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v_ref_451_);
return v_res_458_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_459_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
lean_ctor_set(v___x_464_, 3, v___x_462_);
lean_ctor_set(v___x_464_, 4, v___x_462_);
lean_ctor_set(v___x_464_, 5, v___x_462_);
lean_ctor_set(v___x_464_, 6, v___x_462_);
lean_ctor_set(v___x_464_, 7, v___x_462_);
lean_ctor_set(v___x_464_, 8, v___x_462_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(32u);
v___x_466_ = lean_mk_empty_array_with_capacity(v___x_465_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_468_ = ((size_t)5ULL);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_unsigned_to_nat(32u);
v___x_471_ = lean_mk_empty_array_with_capacity(v___x_470_);
v___x_472_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_473_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___x_471_);
lean_ctor_set(v___x_473_, 2, v___x_469_);
lean_ctor_set(v___x_473_, 3, v___x_469_);
lean_ctor_set_usize(v___x_473_, 4, v___x_468_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = lean_box(1);
v___x_475_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_476_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
lean_ctor_set(v___x_477_, 2, v___x_474_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_499_, lean_object* v_declHint_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; lean_object* v_env_504_; uint8_t v___x_505_; 
v___x_503_ = lean_st_ref_get(v___y_501_);
v_env_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc_ref(v_env_504_);
lean_dec(v___x_503_);
v___x_505_ = l_Lean_Name_isAnonymous(v_declHint_500_);
if (v___x_505_ == 0)
{
uint8_t v_isExporting_506_; 
v_isExporting_506_ = lean_ctor_get_uint8(v_env_504_, sizeof(void*)*8);
if (v_isExporting_506_ == 0)
{
lean_object* v___x_507_; 
lean_dec_ref(v_env_504_);
lean_dec(v_declHint_500_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v_msg_499_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; uint8_t v___x_509_; 
lean_inc_ref(v_env_504_);
v___x_508_ = l_Lean_Environment_setExporting(v_env_504_, v___x_505_);
lean_inc(v_declHint_500_);
lean_inc_ref(v___x_508_);
v___x_509_ = l_Lean_Environment_contains(v___x_508_, v_declHint_500_, v_isExporting_506_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
lean_dec_ref(v___x_508_);
lean_dec_ref(v_env_504_);
lean_dec(v_declHint_500_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v_msg_499_);
return v___x_510_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_c_516_; lean_object* v___x_517_; 
v___x_511_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_512_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_513_ = l_Lean_Options_empty;
v___x_514_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_514_, 0, v___x_508_);
lean_ctor_set(v___x_514_, 1, v___x_511_);
lean_ctor_set(v___x_514_, 2, v___x_512_);
lean_ctor_set(v___x_514_, 3, v___x_513_);
lean_inc(v_declHint_500_);
v___x_515_ = l_Lean_MessageData_ofConstName(v_declHint_500_, v___x_505_);
v_c_516_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_516_, 0, v___x_514_);
lean_ctor_set(v_c_516_, 1, v___x_515_);
v___x_517_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_504_, v_declHint_500_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec_ref(v_env_504_);
lean_dec(v_declHint_500_);
v___x_518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v_c_516_);
v___x_520_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_MessageData_note(v___x_521_);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v_msg_499_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
else
{
lean_object* v_val_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_560_; 
v_val_525_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_560_ == 0)
{
v___x_527_ = v___x_517_;
v_isShared_528_ = v_isSharedCheck_560_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_val_525_);
lean_dec(v___x_517_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_560_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_mod_532_; uint8_t v___x_533_; 
v___x_529_ = lean_box(0);
v___x_530_ = l_Lean_Environment_header(v_env_504_);
lean_dec_ref(v_env_504_);
v___x_531_ = l_Lean_EnvironmentHeader_moduleNames(v___x_530_);
v_mod_532_ = lean_array_get(v___x_529_, v___x_531_, v_val_525_);
lean_dec(v_val_525_);
lean_dec_ref(v___x_531_);
v___x_533_ = l_Lean_isPrivateName(v_declHint_500_);
lean_dec(v_declHint_500_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v_c_516_);
v___x_536_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_MessageData_ofName(v_mod_532_);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_MessageData_note(v___x_541_);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v_msg_499_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 0);
lean_ctor_set(v___x_527_, 0, v___x_543_);
v___x_545_ = v___x_527_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_c_516_);
v___x_549_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = l_Lean_MessageData_ofName(v_mod_532_);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = l_Lean_MessageData_note(v___x_554_);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v_msg_499_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 0);
lean_ctor_set(v___x_527_, 0, v___x_556_);
v___x_558_ = v___x_527_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_561_; 
lean_dec_ref(v_env_504_);
lean_dec(v_declHint_500_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_msg_499_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_562_, lean_object* v_declHint_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_562_, v_declHint_563_, v___y_564_);
lean_dec(v___y_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(lean_object* v_msg_567_, lean_object* v_declHint_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_584_; 
v___x_574_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_567_, v_declHint_568_, v___y_572_);
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_584_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_584_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_584_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_579_ = l_Lean_unknownIdentifierMessageTag;
v___x_580_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_a_575_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_580_);
v___x_582_ = v___x_577_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9___boxed(lean_object* v_msg_585_, lean_object* v_declHint_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_585_, v_declHint_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(lean_object* v_ref_593_, lean_object* v_msg_594_, lean_object* v_declHint_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; lean_object* v_a_602_; lean_object* v___x_603_; 
v___x_601_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_594_, v_declHint_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref(v___x_601_);
v___x_603_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_593_, v_a_602_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_ref_604_, lean_object* v_msg_605_, lean_object* v_declHint_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_604_, v_msg_605_, v_declHint_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v_ref_604_);
return v_res_612_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0));
v___x_615_ = l_Lean_stringToMessageData(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(lean_object* v_ref_619_, lean_object* v_constName_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_626_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1);
v___x_627_ = 0;
lean_inc(v_constName_620_);
v___x_628_ = l_Lean_MessageData_ofConstName(v_constName_620_, v___x_627_);
v___x_629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_626_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_619_, v___x_631_, v_constName_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___boxed(lean_object* v_ref_633_, lean_object* v_constName_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_633_, v_constName_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v_ref_633_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(lean_object* v_constName_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_ref_647_; lean_object* v___x_648_; 
v_ref_647_ = lean_ctor_get(v___y_644_, 5);
v___x_648_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_647_, v_constName_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg___boxed(lean_object* v_constName_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(lean_object* v_constName_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; lean_object* v_env_663_; uint8_t v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_st_ref_get(v___y_660_);
v_env_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_env_663_);
lean_dec(v___x_662_);
v___x_664_ = 0;
lean_inc(v_constName_656_);
v___x_665_ = l_Lean_Environment_find_x3f(v_env_663_, v_constName_656_, v___x_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
return v___x_666_;
}
else
{
lean_object* v_val_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v_constName_656_);
v_val_667_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_665_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_val_667_);
lean_dec(v___x_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 0);
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_val_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4___boxed(lean_object* v_constName_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_constName_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(lean_object* v_binderType_682_, lean_object* v_body_683_, lean_object* v_binderName_684_, uint8_t v_binderInfo_685_, lean_object* v_x_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_binderType_682_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref(v___x_692_);
v___x_694_ = lean_expr_instantiate1(v_body_683_, v_x_686_);
v___x_695_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_694_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; uint8_t v___x_697_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
v___x_697_ = l_Lean_Expr_isErased(v_a_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_709_; 
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_695_, 0);
lean_dec(v_unused_710_);
v___x_699_ = v___x_695_;
v_isShared_700_ = v_isSharedCheck_709_;
goto v_resetjp_698_;
}
else
{
lean_dec(v___x_695_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_709_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_mk_empty_array_with_capacity(v___x_701_);
v___x_703_ = lean_array_push(v___x_702_, v_x_686_);
v___x_704_ = lean_expr_abstract(v_a_696_, v___x_703_);
lean_dec_ref(v___x_703_);
lean_dec(v_a_696_);
v___x_705_ = l_Lean_Expr_lam___override(v_binderName_684_, v_a_693_, v___x_704_, v_binderInfo_685_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_705_);
v___x_707_ = v___x_699_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
else
{
lean_dec(v_a_696_);
lean_dec(v_a_693_);
lean_dec_ref(v_x_686_);
lean_dec(v_binderName_684_);
return v___x_695_;
}
}
else
{
lean_dec(v_a_693_);
lean_dec_ref(v_x_686_);
lean_dec(v_binderName_684_);
return v___x_695_;
}
}
else
{
lean_dec_ref(v_x_686_);
lean_dec(v_binderName_684_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed(lean_object* v_binderType_711_, lean_object* v_body_712_, lean_object* v_binderName_713_, lean_object* v_binderInfo_714_, lean_object* v_x_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
uint8_t v_binderInfo_9698__boxed_721_; lean_object* v_res_722_; 
v_binderInfo_9698__boxed_721_ = lean_unbox(v_binderInfo_714_);
v_res_722_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(v_binderType_711_, v_body_712_, v_binderName_713_, v_binderInfo_9698__boxed_721_, v_x_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_body_712_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(lean_object* v_d_723_, lean_object* v_xs_724_, lean_object* v_body_725_, lean_object* v_binderName_726_, uint8_t v_binderInfo_727_, lean_object* v_x_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
uint8_t v_isBorrowed_734_; lean_object* v___x_735_; 
v_isBorrowed_734_ = l_Lean_isMarkedBorrowed(v_d_723_);
v___x_735_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_d_723_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v_d_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___x_754_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref(v___x_735_);
v___x_754_ = lean_expr_abstract(v_a_736_, v_xs_724_);
lean_dec(v_a_736_);
if (v_isBorrowed_734_ == 0)
{
v_d_738_ = v___x_754_;
v___y_739_ = v___y_729_;
v___y_740_ = v___y_730_;
v___y_741_ = v___y_731_;
v___y_742_ = v___y_732_;
goto v___jp_737_;
}
else
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_markBorrowed(v___x_754_);
v_d_738_ = v___x_755_;
v___y_739_ = v___y_729_;
v___y_740_ = v___y_730_;
v___y_741_ = v___y_731_;
v___y_742_ = v___y_732_;
goto v___jp_737_;
}
v___jp_737_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_array_push(v_xs_724_, v_x_728_);
v___x_744_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_body_725_, v___x_743_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_753_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_753_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = l_Lean_Expr_forallE___override(v_binderName_726_, v_d_738_, v_a_745_, v_binderInfo_727_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_749_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
else
{
lean_dec_ref(v_d_738_);
lean_dec(v_binderName_726_);
return v___x_744_;
}
}
}
else
{
lean_dec_ref(v_x_728_);
lean_dec(v_binderName_726_);
lean_dec_ref(v_body_725_);
lean_dec_ref(v_xs_724_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed(lean_object* v_d_756_, lean_object* v_xs_757_, lean_object* v_body_758_, lean_object* v_binderName_759_, lean_object* v_binderInfo_760_, lean_object* v_x_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
uint8_t v_binderInfo_9720__boxed_767_; lean_object* v_res_768_; 
v_binderInfo_9720__boxed_767_ = lean_unbox(v_binderInfo_760_);
v_res_768_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(v_d_756_, v_xs_757_, v_body_758_, v_binderName_759_, v_binderInfo_9720__boxed_767_, v_x_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(lean_object* v_e_769_, lean_object* v_xs_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
if (lean_obj_tag(v_e_769_) == 7)
{
lean_object* v_binderName_776_; lean_object* v_binderType_777_; lean_object* v_body_778_; uint8_t v_binderInfo_779_; lean_object* v_d_780_; lean_object* v___x_781_; lean_object* v___f_782_; uint8_t v___x_783_; lean_object* v___x_784_; 
v_binderName_776_ = lean_ctor_get(v_e_769_, 0);
lean_inc(v_binderName_776_);
v_binderType_777_ = lean_ctor_get(v_e_769_, 1);
lean_inc_ref(v_binderType_777_);
v_body_778_ = lean_ctor_get(v_e_769_, 2);
lean_inc_ref(v_body_778_);
v_binderInfo_779_ = lean_ctor_get_uint8(v_e_769_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_769_);
v_d_780_ = lean_expr_instantiate_rev(v_binderType_777_, v_xs_770_);
lean_dec_ref(v_binderType_777_);
v___x_781_ = lean_box(v_binderInfo_779_);
lean_inc(v_binderName_776_);
lean_inc_ref(v_d_780_);
v___f_782_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed), 11, 5);
lean_closure_set(v___f_782_, 0, v_d_780_);
lean_closure_set(v___f_782_, 1, v_xs_770_);
lean_closure_set(v___f_782_, 2, v_body_778_);
lean_closure_set(v___f_782_, 3, v_binderName_776_);
lean_closure_set(v___f_782_, 4, v___x_781_);
v___x_783_ = 0;
v___x_784_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_776_, v_binderInfo_779_, v_d_780_, v___f_782_, v___x_783_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_expr_instantiate_rev(v_e_769_, v_xs_770_);
lean_dec_ref(v_e_769_);
v___x_786_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v___x_785_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_795_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_expr_abstract(v_a_787_, v_xs_770_);
lean_dec_ref(v_xs_770_);
lean_dec(v_a_787_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_791_);
v___x_793_ = v___x_789_;
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
else
{
lean_dec_ref(v_xs_770_);
return v___x_786_;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0(void){
_start:
{
lean_object* v___x_796_; lean_object* v_dummy_797_; 
v___x_796_ = lean_box(0);
v_dummy_797_ = l_Lean_Expr_sort___override(v___x_796_);
return v_dummy_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(lean_object* v_type_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; 
lean_inc_ref(v_type_801_);
v___x_807_ = l_Lean_Meta_isProp(v_type_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_874_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_874_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_874_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_874_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint8_t v___x_812_; 
v___x_812_ = lean_unbox(v_a_808_);
lean_dec(v_a_808_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
v___x_813_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
switch(lean_obj_tag(v_a_814_))
{
case 3:
{
lean_dec_ref(v_a_814_);
lean_del_object(v___x_810_);
return v___x_813_;
}
case 4:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec_ref(v___x_813_);
lean_del_object(v___x_810_);
v___x_820_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_821_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_814_, v___x_820_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_821_;
}
case 6:
{
lean_object* v_binderName_822_; lean_object* v_binderType_823_; lean_object* v_body_824_; uint8_t v_binderInfo_825_; lean_object* v___x_826_; lean_object* v___f_827_; uint8_t v___x_828_; lean_object* v___x_829_; 
lean_dec_ref(v___x_813_);
lean_del_object(v___x_810_);
v_binderName_822_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_binderName_822_);
v_binderType_823_ = lean_ctor_get(v_a_814_, 1);
lean_inc_ref(v_binderType_823_);
v_body_824_ = lean_ctor_get(v_a_814_, 2);
lean_inc_ref(v_body_824_);
v_binderInfo_825_ = lean_ctor_get_uint8(v_a_814_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_814_);
v___x_826_ = lean_box(v_binderInfo_825_);
lean_inc(v_binderName_822_);
lean_inc_ref(v_binderType_823_);
v___f_827_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_827_, 0, v_binderType_823_);
lean_closure_set(v___f_827_, 1, v_body_824_);
lean_closure_set(v___f_827_, 2, v_binderName_822_);
lean_closure_set(v___f_827_, 3, v___x_826_);
v___x_828_ = 0;
v___x_829_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_822_, v_binderInfo_825_, v_binderType_823_, v___f_827_, v___x_828_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_829_;
}
case 7:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v___x_813_);
lean_del_object(v___x_810_);
v___x_830_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_831_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_a_814_, v___x_830_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_831_;
}
case 5:
{
lean_object* v_dummy_832_; lean_object* v_nargs_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v___x_813_);
lean_del_object(v___x_810_);
v_dummy_832_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0);
v_nargs_833_ = l_Lean_Expr_getAppNumArgs(v_a_814_);
lean_inc(v_nargs_833_);
v___x_834_ = lean_mk_array(v_nargs_833_, v_dummy_832_);
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_sub(v_nargs_833_, v___x_835_);
lean_dec(v_nargs_833_);
v___x_837_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_a_814_, v___x_834_, v___x_836_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_837_;
}
case 1:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref(v___x_813_);
lean_del_object(v___x_810_);
v___x_838_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0));
v___x_839_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_814_, v___x_838_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_839_;
}
case 11:
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_868_; 
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v___x_813_, 0);
lean_dec(v_unused_869_);
v___x_841_ = v___x_813_;
v_isShared_842_ = v_isSharedCheck_868_;
goto v_resetjp_840_;
}
else
{
lean_dec(v___x_813_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_868_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_typeName_843_; 
v_typeName_843_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_typeName_843_);
if (lean_obj_tag(v_typeName_843_) == 1)
{
lean_object* v_pre_844_; 
v_pre_844_ = lean_ctor_get(v_typeName_843_, 0);
if (lean_obj_tag(v_pre_844_) == 0)
{
lean_object* v_idx_845_; lean_object* v_struct_846_; lean_object* v_str_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_idx_845_ = lean_ctor_get(v_a_814_, 1);
lean_inc(v_idx_845_);
v_struct_846_ = lean_ctor_get(v_a_814_, 2);
lean_inc_ref(v_struct_846_);
lean_dec_ref(v_a_814_);
v_str_847_ = lean_ctor_get(v_typeName_843_, 1);
lean_inc_ref(v_str_847_);
lean_dec_ref(v_typeName_843_);
v___x_848_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1));
v___x_849_ = lean_string_dec_eq(v_str_847_, v___x_848_);
lean_dec_ref(v_str_847_);
if (v___x_849_ == 0)
{
lean_dec_ref(v_struct_846_);
lean_dec(v_idx_845_);
lean_del_object(v___x_841_);
goto v___jp_815_;
}
else
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_nat_dec_eq(v_idx_845_, v___x_850_);
lean_dec(v_idx_845_);
if (v___x_851_ == 0)
{
lean_dec_ref(v_struct_846_);
lean_del_object(v___x_841_);
goto v___jp_815_;
}
else
{
if (lean_obj_tag(v_struct_846_) == 5)
{
lean_object* v_fn_852_; 
v_fn_852_ = lean_ctor_get(v_struct_846_, 0);
lean_inc_ref(v_fn_852_);
lean_dec_ref(v_struct_846_);
if (lean_obj_tag(v_fn_852_) == 4)
{
lean_object* v_declName_853_; 
v_declName_853_ = lean_ctor_get(v_fn_852_, 0);
lean_inc(v_declName_853_);
if (lean_obj_tag(v_declName_853_) == 1)
{
lean_object* v_pre_854_; 
v_pre_854_ = lean_ctor_get(v_declName_853_, 0);
lean_inc(v_pre_854_);
if (lean_obj_tag(v_pre_854_) == 1)
{
lean_object* v_pre_855_; 
v_pre_855_ = lean_ctor_get(v_pre_854_, 0);
if (lean_obj_tag(v_pre_855_) == 0)
{
lean_object* v_us_856_; lean_object* v_str_857_; lean_object* v_str_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_us_856_ = lean_ctor_get(v_fn_852_, 1);
lean_inc(v_us_856_);
lean_dec_ref(v_fn_852_);
v_str_857_ = lean_ctor_get(v_declName_853_, 1);
lean_inc_ref(v_str_857_);
lean_dec_ref(v_declName_853_);
v_str_858_ = lean_ctor_get(v_pre_854_, 1);
lean_inc_ref(v_str_858_);
lean_dec_ref(v_pre_854_);
v___x_859_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2));
v___x_860_ = lean_string_dec_eq(v_str_858_, v___x_859_);
lean_dec_ref(v_str_858_);
if (v___x_860_ == 0)
{
lean_dec_ref(v_str_857_);
lean_dec(v_us_856_);
lean_del_object(v___x_841_);
goto v___jp_815_;
}
else
{
lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3));
v___x_862_ = lean_string_dec_eq(v_str_857_, v___x_861_);
lean_dec_ref(v_str_857_);
if (v___x_862_ == 0)
{
lean_dec(v_us_856_);
lean_del_object(v___x_841_);
goto v___jp_815_;
}
else
{
if (lean_obj_tag(v_us_856_) == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
lean_del_object(v___x_810_);
v___x_863_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_864_ = l_Lean_mkConst(v___x_863_, v_us_856_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_864_);
v___x_866_ = v___x_841_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
else
{
lean_dec(v_us_856_);
lean_del_object(v___x_841_);
goto v___jp_815_;
}
}
}
}
else
{
lean_dec_ref(v_pre_854_);
lean_dec_ref(v_declName_853_);
lean_dec_ref(v_fn_852_);
lean_del_object(v___x_841_);
goto v___jp_815_;
}
}
else
{
lean_dec(v_pre_854_);
lean_dec_ref(v_declName_853_);
lean_dec_ref(v_fn_852_);
lean_del_object(v___x_841_);
goto v___jp_815_;
}
}
else
{
lean_dec_ref(v_fn_852_);
lean_dec(v_declName_853_);
lean_del_object(v___x_841_);
goto v___jp_815_;
}
}
else
{
lean_dec_ref(v_fn_852_);
lean_del_object(v___x_841_);
goto v___jp_815_;
}
}
else
{
lean_dec_ref(v_struct_846_);
lean_del_object(v___x_841_);
goto v___jp_815_;
}
}
}
}
else
{
lean_dec_ref(v_typeName_843_);
lean_del_object(v___x_841_);
lean_dec_ref(v_a_814_);
goto v___jp_815_;
}
}
else
{
lean_dec(v_typeName_843_);
lean_del_object(v___x_841_);
lean_dec_ref(v_a_814_);
goto v___jp_815_;
}
}
}
default: 
{
lean_dec_ref(v___x_813_);
lean_dec(v_a_814_);
goto v___jp_815_;
}
}
v___jp_815_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_816_);
v___x_818_ = v___x_810_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_del_object(v___x_810_);
return v___x_813_;
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_872_; 
lean_dec_ref(v_type_801_);
v___x_870_ = l_Lean_Compiler_LCNF_erasedExpr;
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_870_);
v___x_872_ = v___x_810_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref(v_type_801_);
v_a_875_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_807_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_807_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(lean_object* v_as_883_, size_t v_sz_884_, size_t v_i_885_, lean_object* v_b_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_a_893_; uint8_t v___x_897_; 
v___x_897_ = lean_usize_dec_lt(v_i_885_, v_sz_884_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_b_886_);
return v___x_898_;
}
else
{
lean_object* v_a_899_; lean_object* v___y_901_; lean_object* v___x_930_; 
v_a_899_ = lean_array_uget_borrowed(v_as_883_, v_i_885_);
lean_inc(v_a_899_);
v___x_930_ = l_Lean_Meta_isProp(v_a_899_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; uint8_t v___x_932_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
v___x_932_ = lean_unbox(v_a_931_);
lean_dec(v_a_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
lean_dec_ref(v___x_930_);
lean_inc(v_a_899_);
v___x_933_ = l_Lean_Compiler_LCNF_isPropFormer(v_a_899_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
v___y_901_ = v___x_933_;
goto v___jp_900_;
}
else
{
v___y_901_ = v___x_930_;
goto v___jp_900_;
}
}
else
{
v___y_901_ = v___x_930_;
goto v___jp_900_;
}
v___jp_900_:
{
if (lean_obj_tag(v___y_901_) == 0)
{
lean_object* v_a_902_; uint8_t v___x_903_; 
v_a_902_ = lean_ctor_get(v___y_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref(v___y_901_);
v___x_903_ = lean_unbox(v_a_902_);
lean_dec(v_a_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_inc(v_a_899_);
v___x_904_ = l_Lean_Meta_isTypeFormer(v_a_899_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; uint8_t v___x_906_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref(v___x_904_);
v___x_906_ = lean_unbox(v_a_905_);
lean_dec(v_a_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_908_ = l_Lean_Expr_app___override(v_b_886_, v___x_907_);
v_a_893_ = v___x_908_;
goto v___jp_892_;
}
else
{
lean_object* v___x_909_; 
lean_inc(v_a_899_);
v___x_909_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_a_899_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref(v___x_909_);
v___x_911_ = l_Lean_Expr_app___override(v_b_886_, v_a_910_);
v_a_893_ = v___x_911_;
goto v___jp_892_;
}
else
{
lean_dec_ref(v_b_886_);
return v___x_909_;
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v_b_886_);
v_a_912_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_904_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_904_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_921_ = l_Lean_Expr_app___override(v_b_886_, v___x_920_);
v_a_893_ = v___x_921_;
goto v___jp_892_;
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec_ref(v_b_886_);
v_a_922_ = lean_ctor_get(v___y_901_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___y_901_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___y_901_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___y_901_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
v___jp_892_:
{
size_t v___x_894_; size_t v___x_895_; 
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_add(v_i_885_, v___x_894_);
v_i_885_ = v___x_895_;
v_b_886_ = v_a_893_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0));
v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(lean_object* v_f_937_, lean_object* v_args_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_fNew_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; 
switch(lean_obj_tag(v_f_937_))
{
case 4:
{
lean_object* v_declName_953_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___x_977_; lean_object* v_env_978_; uint8_t v_isExporting_979_; 
v_declName_953_ = lean_ctor_get(v_f_937_, 0);
v___x_977_ = lean_st_ref_get(v_a_942_);
v_env_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc_ref(v_env_978_);
lean_dec(v___x_977_);
v_isExporting_979_ = lean_ctor_get_uint8(v_env_978_, sizeof(void*)*8);
lean_dec_ref(v_env_978_);
if (v_isExporting_979_ == 0)
{
v___y_955_ = v_a_939_;
v___y_956_ = v_a_940_;
v___y_957_ = v_a_941_;
v___y_958_ = v_a_942_;
goto v___jp_954_;
}
else
{
uint8_t v___x_980_; 
v___x_980_ = l_Lean_isPrivateName(v_declName_953_);
if (v___x_980_ == 0)
{
v___y_955_ = v_a_939_;
v___y_956_ = v_a_940_;
v___y_957_ = v_a_941_;
v___y_958_ = v_a_942_;
goto v___jp_954_;
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1);
v___x_982_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_981_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_dec_ref(v___x_982_);
v___y_955_ = v_a_939_;
v___y_956_ = v_a_940_;
v___y_957_ = v_a_941_;
v___y_958_ = v_a_942_;
goto v___jp_954_;
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec_ref(v_f_937_);
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
v___jp_954_:
{
lean_object* v___x_959_; 
lean_inc(v_declName_953_);
v___x_959_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_declName_953_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_968_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
if (lean_obj_tag(v_a_960_) == 5)
{
lean_dec_ref(v_a_960_);
lean_del_object(v___x_962_);
v_fNew_945_ = v_f_937_;
v___y_946_ = v___y_955_;
v___y_947_ = v___y_956_;
v___y_948_ = v___y_957_;
v___y_949_ = v___y_958_;
goto v___jp_944_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_966_; 
lean_dec(v_a_960_);
lean_dec_ref(v_f_937_);
v___x_964_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
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
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_f_937_);
v_a_969_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_959_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_959_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
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
}
case 1:
{
v_fNew_945_ = v_f_937_;
v___y_946_ = v_a_939_;
v___y_947_ = v_a_940_;
v___y_948_ = v_a_941_;
v___y_949_ = v_a_942_;
goto v___jp_944_;
}
default: 
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec_ref(v_f_937_);
v___x_991_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
v___jp_944_:
{
size_t v_sz_950_; size_t v___x_951_; lean_object* v___x_952_; 
v_sz_950_ = lean_array_size(v_args_938_);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_args_938_, v_sz_950_, v___x_951_, v_fNew_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
if (lean_obj_tag(v_x_993_) == 5)
{
lean_object* v_fn_1001_; lean_object* v_arg_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_fn_1001_ = lean_ctor_get(v_x_993_, 0);
lean_inc_ref(v_fn_1001_);
v_arg_1002_ = lean_ctor_get(v_x_993_, 1);
lean_inc_ref(v_arg_1002_);
lean_dec_ref(v_x_993_);
v___x_1003_ = lean_array_set(v_x_994_, v_x_995_, v_arg_1002_);
v___x_1004_ = lean_unsigned_to_nat(1u);
v___x_1005_ = lean_nat_sub(v_x_995_, v___x_1004_);
lean_dec(v_x_995_);
v_x_993_ = v_fn_1001_;
v_x_994_ = v___x_1003_;
v_x_995_ = v___x_1005_;
goto _start;
}
else
{
lean_object* v___x_1007_; 
lean_dec(v_x_995_);
v___x_1007_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_x_993_, v_x_994_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec_ref(v_x_994_);
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0___boxed(lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_x_1008_, v_x_1009_, v_x_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___boxed(lean_object* v_e_1017_, lean_object* v_xs_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_e_1017_, v_xs_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___boxed(lean_object* v_f_1025_, lean_object* v_args_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_f_1025_, v_args_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec_ref(v_args_1026_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3___boxed(lean_object* v_as_1033_, lean_object* v_sz_1034_, lean_object* v_i_1035_, lean_object* v_b_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
size_t v_sz_boxed_1042_; size_t v_i_boxed_1043_; lean_object* v_res_1044_; 
v_sz_boxed_1042_ = lean_unbox_usize(v_sz_1034_);
lean_dec(v_sz_1034_);
v_i_boxed_1043_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_res_1044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_as_1033_, v_sz_boxed_1042_, v_i_boxed_1043_, v_b_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec_ref(v_as_1033_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed(lean_object* v_type_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(lean_object* v_00_u03b1_1052_, lean_object* v_msg_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___boxed(lean_object* v_00_u03b1_1060_, lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(v_00_u03b1_1060_, v_msg_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(lean_object* v_00_u03b1_1068_, lean_object* v_constName_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___boxed(lean_object* v_00_u03b1_1076_, lean_object* v_constName_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(v_00_u03b1_1076_, v_constName_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(lean_object* v_00_u03b1_1084_, lean_object* v_ref_1085_, lean_object* v_constName_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_1085_, v_constName_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_ref_1094_, lean_object* v_constName_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(v_00_u03b1_1093_, v_ref_1094_, v_constName_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v_ref_1094_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(lean_object* v_00_u03b1_1102_, lean_object* v_ref_1103_, lean_object* v_msg_1104_, lean_object* v_declHint_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_1103_, v_msg_1104_, v_declHint_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_ref_1113_, lean_object* v_msg_1114_, lean_object* v_declHint_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(v_00_u03b1_1112_, v_ref_1113_, v_msg_1114_, v_declHint_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v_ref_1113_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(lean_object* v_msg_1122_, lean_object* v_declHint_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_1122_, v_declHint_1123_, v___y_1127_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_1130_, lean_object* v_declHint_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(v_msg_1130_, v_declHint_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(lean_object* v_00_u03b1_1138_, lean_object* v_ref_1139_, lean_object* v_msg_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_1139_, v_msg_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1147_, lean_object* v_ref_1148_, lean_object* v_msg_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(v_00_u03b1_1147_, v_ref_1148_, v_msg_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v_ref_1148_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(lean_object* v___y_1156_, uint8_t v_isExporting_1157_, lean_object* v___x_1158_, lean_object* v___y_1159_, lean_object* v___x_1160_, lean_object* v_a_x3f_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v_env_1164_; lean_object* v_nextMacroScope_1165_; lean_object* v_ngen_1166_; lean_object* v_auxDeclNGen_1167_; lean_object* v_traceState_1168_; lean_object* v_messages_1169_; lean_object* v_infoState_1170_; lean_object* v_snapshotTasks_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1196_; 
v___x_1163_ = lean_st_ref_take(v___y_1156_);
v_env_1164_ = lean_ctor_get(v___x_1163_, 0);
v_nextMacroScope_1165_ = lean_ctor_get(v___x_1163_, 1);
v_ngen_1166_ = lean_ctor_get(v___x_1163_, 2);
v_auxDeclNGen_1167_ = lean_ctor_get(v___x_1163_, 3);
v_traceState_1168_ = lean_ctor_get(v___x_1163_, 4);
v_messages_1169_ = lean_ctor_get(v___x_1163_, 6);
v_infoState_1170_ = lean_ctor_get(v___x_1163_, 7);
v_snapshotTasks_1171_ = lean_ctor_get(v___x_1163_, 8);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v___x_1163_, 5);
lean_dec(v_unused_1197_);
v___x_1173_ = v___x_1163_;
v_isShared_1174_ = v_isSharedCheck_1196_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snapshotTasks_1171_);
lean_inc(v_infoState_1170_);
lean_inc(v_messages_1169_);
lean_inc(v_traceState_1168_);
lean_inc(v_auxDeclNGen_1167_);
lean_inc(v_ngen_1166_);
lean_inc(v_nextMacroScope_1165_);
lean_inc(v_env_1164_);
lean_dec(v___x_1163_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1196_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = l_Lean_Environment_setExporting(v_env_1164_, v_isExporting_1157_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 5, v___x_1158_);
lean_ctor_set(v___x_1173_, 0, v___x_1175_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_nextMacroScope_1165_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_ngen_1166_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v_auxDeclNGen_1167_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v_traceState_1168_);
lean_ctor_set(v_reuseFailAlloc_1195_, 5, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1195_, 6, v_messages_1169_);
lean_ctor_set(v_reuseFailAlloc_1195_, 7, v_infoState_1170_);
lean_ctor_set(v_reuseFailAlloc_1195_, 8, v_snapshotTasks_1171_);
v___x_1177_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_mctx_1180_; lean_object* v_zetaDeltaFVarIds_1181_; lean_object* v_postponed_1182_; lean_object* v_diag_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1193_; 
v___x_1178_ = lean_st_ref_set(v___y_1156_, v___x_1177_);
v___x_1179_ = lean_st_ref_take(v___y_1159_);
v_mctx_1180_ = lean_ctor_get(v___x_1179_, 0);
v_zetaDeltaFVarIds_1181_ = lean_ctor_get(v___x_1179_, 2);
v_postponed_1182_ = lean_ctor_get(v___x_1179_, 3);
v_diag_1183_ = lean_ctor_get(v___x_1179_, 4);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v___x_1179_, 1);
lean_dec(v_unused_1194_);
v___x_1185_ = v___x_1179_;
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_diag_1183_);
lean_inc(v_postponed_1182_);
lean_inc(v_zetaDeltaFVarIds_1181_);
lean_inc(v_mctx_1180_);
lean_dec(v___x_1179_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1160_);
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_mctx_1180_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_zetaDeltaFVarIds_1181_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_postponed_1182_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v_diag_1183_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = lean_st_ref_set(v___y_1159_, v___x_1188_);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0___boxed(lean_object* v___y_1198_, lean_object* v_isExporting_1199_, lean_object* v___x_1200_, lean_object* v___y_1201_, lean_object* v___x_1202_, lean_object* v_a_x3f_1203_, lean_object* v___y_1204_){
_start:
{
uint8_t v_isExporting_boxed_1205_; lean_object* v_res_1206_; 
v_isExporting_boxed_1205_ = lean_unbox(v_isExporting_1199_);
v_res_1206_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1198_, v_isExporting_boxed_1205_, v___x_1200_, v___y_1201_, v___x_1202_, v_a_x3f_1203_);
lean_dec(v_a_x3f_1203_);
lean_dec(v___y_1201_);
lean_dec(v___y_1198_);
return v_res_1206_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
v___x_1213_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
lean_ctor_set(v___x_1213_, 2, v___x_1212_);
lean_ctor_set(v___x_1213_, 3, v___x_1212_);
lean_ctor_set(v___x_1213_, 4, v___x_1212_);
lean_ctor_set(v___x_1213_, 5, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(lean_object* v_x_1214_, uint8_t v_isExporting_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v_env_1222_; uint8_t v_isExporting_1223_; lean_object* v___x_1224_; lean_object* v_env_1225_; lean_object* v_nextMacroScope_1226_; lean_object* v_ngen_1227_; lean_object* v_auxDeclNGen_1228_; lean_object* v_traceState_1229_; lean_object* v_messages_1230_; lean_object* v_infoState_1231_; lean_object* v_snapshotTasks_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1286_; 
v___x_1221_ = lean_st_ref_get(v___y_1219_);
v_env_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc_ref(v_env_1222_);
lean_dec(v___x_1221_);
v_isExporting_1223_ = lean_ctor_get_uint8(v_env_1222_, sizeof(void*)*8);
lean_dec_ref(v_env_1222_);
v___x_1224_ = lean_st_ref_take(v___y_1219_);
v_env_1225_ = lean_ctor_get(v___x_1224_, 0);
v_nextMacroScope_1226_ = lean_ctor_get(v___x_1224_, 1);
v_ngen_1227_ = lean_ctor_get(v___x_1224_, 2);
v_auxDeclNGen_1228_ = lean_ctor_get(v___x_1224_, 3);
v_traceState_1229_ = lean_ctor_get(v___x_1224_, 4);
v_messages_1230_ = lean_ctor_get(v___x_1224_, 6);
v_infoState_1231_ = lean_ctor_get(v___x_1224_, 7);
v_snapshotTasks_1232_ = lean_ctor_get(v___x_1224_, 8);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v___x_1224_, 5);
lean_dec(v_unused_1287_);
v___x_1234_ = v___x_1224_;
v_isShared_1235_ = v_isSharedCheck_1286_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_snapshotTasks_1232_);
lean_inc(v_infoState_1231_);
lean_inc(v_messages_1230_);
lean_inc(v_traceState_1229_);
lean_inc(v_auxDeclNGen_1228_);
lean_inc(v_ngen_1227_);
lean_inc(v_nextMacroScope_1226_);
lean_inc(v_env_1225_);
lean_dec(v___x_1224_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1286_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1236_ = l_Lean_Environment_setExporting(v_env_1225_, v_isExporting_1215_);
v___x_1237_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 5, v___x_1237_);
lean_ctor_set(v___x_1234_, 0, v___x_1236_);
v___x_1239_ = v___x_1234_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_nextMacroScope_1226_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_ngen_1227_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_auxDeclNGen_1228_);
lean_ctor_set(v_reuseFailAlloc_1285_, 4, v_traceState_1229_);
lean_ctor_set(v_reuseFailAlloc_1285_, 5, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1285_, 6, v_messages_1230_);
lean_ctor_set(v_reuseFailAlloc_1285_, 7, v_infoState_1231_);
lean_ctor_set(v_reuseFailAlloc_1285_, 8, v_snapshotTasks_1232_);
v___x_1239_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_mctx_1242_; lean_object* v_zetaDeltaFVarIds_1243_; lean_object* v_postponed_1244_; lean_object* v_diag_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1283_; 
v___x_1240_ = lean_st_ref_set(v___y_1219_, v___x_1239_);
v___x_1241_ = lean_st_ref_take(v___y_1217_);
v_mctx_1242_ = lean_ctor_get(v___x_1241_, 0);
v_zetaDeltaFVarIds_1243_ = lean_ctor_get(v___x_1241_, 2);
v_postponed_1244_ = lean_ctor_get(v___x_1241_, 3);
v_diag_1245_ = lean_ctor_get(v___x_1241_, 4);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v___x_1241_, 1);
lean_dec(v_unused_1284_);
v___x_1247_ = v___x_1241_;
v_isShared_1248_ = v_isSharedCheck_1283_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_diag_1245_);
lean_inc(v_postponed_1244_);
lean_inc(v_zetaDeltaFVarIds_1243_);
lean_inc(v_mctx_1242_);
lean_dec(v___x_1241_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1283_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v___x_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_mctx_1242_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_zetaDeltaFVarIds_1243_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_postponed_1244_);
lean_ctor_set(v_reuseFailAlloc_1282_, 4, v_diag_1245_);
v___x_1251_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v_r_1253_; 
v___x_1252_ = lean_st_ref_set(v___y_1217_, v___x_1251_);
lean_inc(v___y_1219_);
lean_inc_ref(v___y_1218_);
lean_inc(v___y_1217_);
lean_inc_ref(v___y_1216_);
v_r_1253_ = lean_apply_5(v_x_1214_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, lean_box(0));
if (lean_obj_tag(v_r_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1270_; 
v_a_1254_ = lean_ctor_get(v_r_1253_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_r_1253_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1256_ = v_r_1253_;
v_isShared_1257_ = v_isSharedCheck_1270_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v_r_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1270_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
lean_inc(v_a_1254_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 1);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
v___x_1260_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1219_, v_isExporting_1223_, v___x_1237_, v___y_1217_, v___x_1249_, v___x_1259_);
lean_dec_ref(v___x_1259_);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v___x_1260_, 0);
lean_dec(v_unused_1268_);
v___x_1262_ = v___x_1260_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_dec(v___x_1260_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v_a_1254_);
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1254_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
v_a_1271_ = lean_ctor_get(v_r_1253_, 0);
lean_inc(v_a_1271_);
lean_dec_ref(v_r_1253_);
v___x_1272_ = lean_box(0);
v___x_1273_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_1219_, v_isExporting_1223_, v___x_1237_, v___y_1217_, v___x_1249_, v___x_1272_);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v___x_1273_, 0);
lean_dec(v_unused_1281_);
v___x_1275_ = v___x_1273_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v___x_1273_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 1);
lean_ctor_set(v___x_1275_, 0, v_a_1271_);
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1271_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___boxed(lean_object* v_x_1288_, lean_object* v_isExporting_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
uint8_t v_isExporting_boxed_1295_; lean_object* v_res_1296_; 
v_isExporting_boxed_1295_ = lean_unbox(v_isExporting_1289_);
v_res_1296_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1288_, v_isExporting_boxed_1295_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(lean_object* v_00_u03b1_1297_, lean_object* v_x_1298_, uint8_t v_isExporting_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v_x_1298_, v_isExporting_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_x_1307_, lean_object* v_isExporting_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
uint8_t v_isExporting_boxed_1314_; lean_object* v_res_1315_; 
v_isExporting_boxed_1314_ = lean_unbox(v_isExporting_1308_);
v_res_1315_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(v_00_u03b1_1306_, v_x_1307_, v_isExporting_boxed_1314_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
return v_res_1315_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(lean_object* v_opts_1316_, lean_object* v_opt_1317_){
_start:
{
lean_object* v_name_1318_; lean_object* v_defValue_1319_; lean_object* v_map_1320_; lean_object* v___x_1321_; 
v_name_1318_ = lean_ctor_get(v_opt_1317_, 0);
v_defValue_1319_ = lean_ctor_get(v_opt_1317_, 1);
v_map_1320_ = lean_ctor_get(v_opts_1316_, 0);
v___x_1321_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1320_, v_name_1318_);
if (lean_obj_tag(v___x_1321_) == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_unbox(v_defValue_1319_);
return v___x_1322_;
}
else
{
lean_object* v_val_1323_; 
v_val_1323_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_val_1323_);
lean_dec_ref(v___x_1321_);
if (lean_obj_tag(v_val_1323_) == 1)
{
uint8_t v_v_1324_; 
v_v_1324_ = lean_ctor_get_uint8(v_val_1323_, 0);
lean_dec_ref(v_val_1323_);
return v_v_1324_;
}
else
{
uint8_t v___x_1325_; 
lean_dec(v_val_1323_);
v___x_1325_ = lean_unbox(v_defValue_1319_);
return v___x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5___boxed(lean_object* v_opts_1326_, lean_object* v_opt_1327_){
_start:
{
uint8_t v_res_1328_; lean_object* v_r_1329_; 
v_res_1328_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v_opts_1326_, v_opt_1327_);
lean_dec_ref(v_opt_1327_);
lean_dec_ref(v_opts_1326_);
v_r_1329_ = lean_box(v_res_1328_);
return v_r_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(lean_object* v_opts_1330_, lean_object* v_opt_1331_){
_start:
{
lean_object* v_name_1332_; lean_object* v_defValue_1333_; lean_object* v_map_1334_; lean_object* v___x_1335_; 
v_name_1332_ = lean_ctor_get(v_opt_1331_, 0);
v_defValue_1333_ = lean_ctor_get(v_opt_1331_, 1);
v_map_1334_ = lean_ctor_get(v_opts_1330_, 0);
v___x_1335_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1334_, v_name_1332_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_inc(v_defValue_1333_);
return v_defValue_1333_;
}
else
{
lean_object* v_val_1336_; 
v_val_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_val_1336_);
lean_dec_ref(v___x_1335_);
if (lean_obj_tag(v_val_1336_) == 3)
{
lean_object* v_v_1337_; 
v_v_1337_ = lean_ctor_get(v_val_1336_, 0);
lean_inc(v_v_1337_);
lean_dec_ref(v_val_1336_);
return v_v_1337_;
}
else
{
lean_dec(v_val_1336_);
lean_inc(v_defValue_1333_);
return v_defValue_1333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6___boxed(lean_object* v_opts_1338_, lean_object* v_opt_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(v_opts_1338_, v_opt_1339_);
lean_dec_ref(v_opt_1339_);
lean_dec_ref(v_opts_1338_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0(lean_object* v_a_1341_, lean_object* v_diag_1342_, lean_object* v_a_x3f_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v_mctx_1346_; lean_object* v_cache_1347_; lean_object* v_zetaDeltaFVarIds_1348_; lean_object* v_postponed_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1359_; 
v___x_1345_ = lean_st_ref_take(v_a_1341_);
v_mctx_1346_ = lean_ctor_get(v___x_1345_, 0);
v_cache_1347_ = lean_ctor_get(v___x_1345_, 1);
v_zetaDeltaFVarIds_1348_ = lean_ctor_get(v___x_1345_, 2);
v_postponed_1349_ = lean_ctor_get(v___x_1345_, 3);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v___x_1345_, 4);
lean_dec(v_unused_1360_);
v___x_1351_ = v___x_1345_;
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_postponed_1349_);
lean_inc(v_zetaDeltaFVarIds_1348_);
lean_inc(v_cache_1347_);
lean_inc(v_mctx_1346_);
lean_dec(v___x_1345_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 4, v_diag_1342_);
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_mctx_1346_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_cache_1347_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_zetaDeltaFVarIds_1348_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_postponed_1349_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v_diag_1342_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = lean_st_ref_set(v_a_1341_, v___x_1354_);
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(lean_object* v_a_1361_, lean_object* v_diag_1362_, lean_object* v_a_x3f_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1361_, v_diag_1362_, v_a_x3f_1363_);
lean_dec(v_a_x3f_1363_);
lean_dec(v_a_1361_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0(lean_object* v_ps_1366_, lean_object* v_k_1367_, lean_object* v_v_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_k_1367_);
lean_ctor_set(v___x_1369_, 1, v_v_1368_);
v___x_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v_ps_1366_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(lean_object* v_f_1371_, lean_object* v_keys_1372_, lean_object* v_vals_1373_, lean_object* v_i_1374_, lean_object* v_acc_1375_){
_start:
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = lean_array_get_size(v_keys_1372_);
v___x_1377_ = lean_nat_dec_lt(v_i_1374_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec(v_i_1374_);
lean_dec(v_f_1371_);
return v_acc_1375_;
}
else
{
lean_object* v_k_1378_; lean_object* v_v_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_k_1378_ = lean_array_fget_borrowed(v_keys_1372_, v_i_1374_);
v_v_1379_ = lean_array_fget_borrowed(v_vals_1373_, v_i_1374_);
lean_inc(v_f_1371_);
lean_inc(v_v_1379_);
lean_inc(v_k_1378_);
v___x_1380_ = lean_apply_3(v_f_1371_, v_acc_1375_, v_k_1378_, v_v_1379_);
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_nat_add(v_i_1374_, v___x_1381_);
lean_dec(v_i_1374_);
v_i_1374_ = v___x_1382_;
v_acc_1375_ = v___x_1380_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_f_1384_, lean_object* v_keys_1385_, lean_object* v_vals_1386_, lean_object* v_i_1387_, lean_object* v_acc_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1384_, v_keys_1385_, v_vals_1386_, v_i_1387_, v_acc_1388_);
lean_dec_ref(v_vals_1386_);
lean_dec_ref(v_keys_1385_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(lean_object* v_f_1390_, lean_object* v_x_1391_, lean_object* v_x_1392_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
lean_object* v_es_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_es_1393_ = lean_ctor_get(v_x_1391_, 0);
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = lean_array_get_size(v_es_1393_);
v___x_1396_ = lean_nat_dec_lt(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_dec(v_f_1390_);
return v_x_1392_;
}
else
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_nat_dec_le(v___x_1395_, v___x_1395_);
if (v___x_1397_ == 0)
{
if (v___x_1396_ == 0)
{
lean_dec(v_f_1390_);
return v_x_1392_;
}
else
{
size_t v___x_1398_; size_t v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = lean_usize_of_nat(v___x_1395_);
v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1390_, v_es_1393_, v___x_1398_, v___x_1399_, v_x_1392_);
return v___x_1400_;
}
}
else
{
size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = lean_usize_of_nat(v___x_1395_);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1390_, v_es_1393_, v___x_1401_, v___x_1402_, v_x_1392_);
return v___x_1403_;
}
}
}
else
{
lean_object* v_ks_1404_; lean_object* v_vs_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v_ks_1404_ = lean_ctor_get(v_x_1391_, 0);
v_vs_1405_ = lean_ctor_get(v_x_1391_, 1);
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1390_, v_ks_1404_, v_vs_1405_, v___x_1406_, v_x_1392_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(lean_object* v_f_1408_, lean_object* v_as_1409_, size_t v_i_1410_, size_t v_stop_1411_, lean_object* v_b_1412_){
_start:
{
lean_object* v___y_1414_; uint8_t v___x_1418_; 
v___x_1418_ = lean_usize_dec_eq(v_i_1410_, v_stop_1411_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_array_uget_borrowed(v_as_1409_, v_i_1410_);
switch(lean_obj_tag(v___x_1419_))
{
case 0:
{
lean_object* v_key_1420_; lean_object* v_val_1421_; lean_object* v___x_1422_; 
v_key_1420_ = lean_ctor_get(v___x_1419_, 0);
v_val_1421_ = lean_ctor_get(v___x_1419_, 1);
lean_inc(v_f_1408_);
lean_inc(v_val_1421_);
lean_inc(v_key_1420_);
v___x_1422_ = lean_apply_3(v_f_1408_, v_b_1412_, v_key_1420_, v_val_1421_);
v___y_1414_ = v___x_1422_;
goto v___jp_1413_;
}
case 1:
{
lean_object* v_node_1423_; lean_object* v___x_1424_; 
v_node_1423_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_f_1408_);
v___x_1424_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1408_, v_node_1423_, v_b_1412_);
v___y_1414_ = v___x_1424_;
goto v___jp_1413_;
}
default: 
{
v___y_1414_ = v_b_1412_;
goto v___jp_1413_;
}
}
}
else
{
lean_dec(v_f_1408_);
return v_b_1412_;
}
v___jp_1413_:
{
size_t v___x_1415_; size_t v___x_1416_; 
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_add(v_i_1410_, v___x_1415_);
v_i_1410_ = v___x_1416_;
v_b_1412_ = v___y_1414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg___boxed(lean_object* v_f_1425_, lean_object* v_as_1426_, lean_object* v_i_1427_, lean_object* v_stop_1428_, lean_object* v_b_1429_){
_start:
{
size_t v_i_boxed_1430_; size_t v_stop_boxed_1431_; lean_object* v_res_1432_; 
v_i_boxed_1430_ = lean_unbox_usize(v_i_1427_);
lean_dec(v_i_1427_);
v_stop_boxed_1431_ = lean_unbox_usize(v_stop_1428_);
lean_dec(v_stop_1428_);
v_res_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1425_, v_as_1426_, v_i_boxed_1430_, v_stop_boxed_1431_, v_b_1429_);
lean_dec_ref(v_as_1426_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_f_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1433_, v_x_1434_, v_x_1435_);
lean_dec_ref(v_x_1434_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0(lean_object* v_f_1437_, lean_object* v_x1_1438_, lean_object* v_x2_1439_, lean_object* v_x3_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_apply_3(v_f_1437_, v_x1_1438_, v_x2_1439_, v_x3_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(lean_object* v_map_1442_, lean_object* v_f_1443_, lean_object* v_init_1444_){
_start:
{
lean_object* v___f_1445_; lean_object* v___x_1446_; 
v___f_1445_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1445_, 0, v_f_1443_);
v___x_1446_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v___f_1445_, v_map_1442_, v_init_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___boxed(lean_object* v_map_1447_, lean_object* v_f_1448_, lean_object* v_init_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_1447_, v_f_1448_, v_init_1449_);
lean_dec_ref(v_map_1447_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(lean_object* v_m_1452_){
_start:
{
lean_object* v___f_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___f_1453_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0));
v___x_1454_ = lean_box(0);
v___x_1455_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_m_1452_, v___f_1453_, v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___boxed(lean_object* v_m_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1456_);
lean_dec_ref(v_m_1456_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(lean_object* v_o_1461_, lean_object* v_k_1462_, uint8_t v_v_1463_){
_start:
{
lean_object* v_map_1464_; uint8_t v_hasTrace_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1479_; 
v_map_1464_ = lean_ctor_get(v_o_1461_, 0);
v_hasTrace_1465_ = lean_ctor_get_uint8(v_o_1461_, sizeof(void*)*1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_o_1461_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1467_ = v_o_1461_;
v_isShared_1468_ = v_isSharedCheck_1479_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_map_1464_);
lean_dec(v_o_1461_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1479_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1469_, 0, v_v_1463_);
lean_inc(v_k_1462_);
v___x_1470_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1462_, v___x_1469_, v_map_1464_);
if (v_hasTrace_1465_ == 0)
{
lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1474_; 
v___x_1471_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1));
v___x_1472_ = l_Lean_Name_isPrefixOf(v___x_1471_, v_k_1462_);
lean_dec(v_k_1462_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1470_);
v___x_1474_ = v___x_1467_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1470_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*1, v___x_1472_);
return v___x_1474_;
}
}
else
{
lean_object* v___x_1477_; 
lean_dec(v_k_1462_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1470_);
v___x_1477_ = v___x_1467_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1470_);
lean_ctor_set_uint8(v_reuseFailAlloc_1478_, sizeof(void*)*1, v_hasTrace_1465_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___boxed(lean_object* v_o_1480_, lean_object* v_k_1481_, lean_object* v_v_1482_){
_start:
{
uint8_t v_v_boxed_1483_; lean_object* v_res_1484_; 
v_v_boxed_1483_ = lean_unbox(v_v_1482_);
v_res_1484_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(v_o_1480_, v_k_1481_, v_v_boxed_1483_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(lean_object* v_opts_1485_, lean_object* v_opt_1486_, uint8_t v_val_1487_){
_start:
{
lean_object* v_name_1488_; lean_object* v___x_1489_; 
v_name_1488_ = lean_ctor_get(v_opt_1486_, 0);
lean_inc(v_name_1488_);
lean_dec_ref(v_opt_1486_);
v___x_1489_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(v_opts_1485_, v_name_1488_, v_val_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4___boxed(lean_object* v_opts_1490_, lean_object* v_opt_1491_, lean_object* v_val_1492_){
_start:
{
uint8_t v_val_boxed_1493_; lean_object* v_res_1494_; 
v_val_boxed_1493_ = lean_unbox(v_val_1492_);
v_res_1494_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v_opts_1490_, v_opt_1491_, v_val_boxed_1493_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(lean_object* v_keys_1495_, lean_object* v_vals_1496_, lean_object* v_i_1497_, lean_object* v_k_1498_){
_start:
{
lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1499_ = lean_array_get_size(v_keys_1495_);
v___x_1500_ = lean_nat_dec_lt(v_i_1497_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_dec(v_i_1497_);
v___x_1501_ = lean_box(0);
return v___x_1501_;
}
else
{
lean_object* v_k_x27_1502_; uint8_t v___x_1503_; 
v_k_x27_1502_ = lean_array_fget_borrowed(v_keys_1495_, v_i_1497_);
v___x_1503_ = lean_name_eq(v_k_1498_, v_k_x27_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_unsigned_to_nat(1u);
v___x_1505_ = lean_nat_add(v_i_1497_, v___x_1504_);
lean_dec(v_i_1497_);
v_i_1497_ = v___x_1505_;
goto _start;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_array_fget_borrowed(v_vals_1496_, v_i_1497_);
lean_dec(v_i_1497_);
lean_inc(v___x_1507_);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_keys_1509_, lean_object* v_vals_1510_, lean_object* v_i_1511_, lean_object* v_k_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_keys_1509_, v_vals_1510_, v_i_1511_, v_k_1512_);
lean_dec(v_k_1512_);
lean_dec_ref(v_vals_1510_);
lean_dec_ref(v_keys_1509_);
return v_res_1513_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1514_; size_t v___x_1515_; size_t v___x_1516_; 
v___x_1514_ = ((size_t)5ULL);
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_shift_left(v___x_1515_, v___x_1514_);
return v___x_1516_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; 
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0);
v___x_1519_ = lean_usize_sub(v___x_1518_, v___x_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(lean_object* v_x_1520_, size_t v_x_1521_, lean_object* v_x_1522_){
_start:
{
if (lean_obj_tag(v_x_1520_) == 0)
{
lean_object* v_es_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1544_; 
v_es_1523_ = lean_ctor_get(v_x_1520_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_x_1520_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1525_ = v_x_1520_;
v_isShared_1526_ = v_isSharedCheck_1544_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_es_1523_);
lean_dec(v_x_1520_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1544_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; lean_object* v_j_1531_; lean_object* v___x_1532_; 
v___x_1527_ = lean_box(2);
v___x_1528_ = ((size_t)5ULL);
v___x_1529_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1);
v___x_1530_ = lean_usize_land(v_x_1521_, v___x_1529_);
v_j_1531_ = lean_usize_to_nat(v___x_1530_);
v___x_1532_ = lean_array_get(v___x_1527_, v_es_1523_, v_j_1531_);
lean_dec(v_j_1531_);
lean_dec_ref(v_es_1523_);
switch(lean_obj_tag(v___x_1532_))
{
case 0:
{
lean_object* v_key_1533_; lean_object* v_val_1534_; uint8_t v___x_1535_; 
v_key_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_key_1533_);
v_val_1534_ = lean_ctor_get(v___x_1532_, 1);
lean_inc(v_val_1534_);
lean_dec_ref(v___x_1532_);
v___x_1535_ = lean_name_eq(v_x_1522_, v_key_1533_);
lean_dec(v_key_1533_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; 
lean_dec(v_val_1534_);
lean_del_object(v___x_1525_);
v___x_1536_ = lean_box(0);
return v___x_1536_;
}
else
{
lean_object* v___x_1538_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set_tag(v___x_1525_, 1);
lean_ctor_set(v___x_1525_, 0, v_val_1534_);
v___x_1538_ = v___x_1525_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_val_1534_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
case 1:
{
lean_object* v_node_1540_; size_t v___x_1541_; 
lean_del_object(v___x_1525_);
v_node_1540_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_node_1540_);
lean_dec_ref(v___x_1532_);
v___x_1541_ = lean_usize_shift_right(v_x_1521_, v___x_1528_);
v_x_1520_ = v_node_1540_;
v_x_1521_ = v___x_1541_;
goto _start;
}
default: 
{
lean_object* v___x_1543_; 
lean_del_object(v___x_1525_);
v___x_1543_ = lean_box(0);
return v___x_1543_;
}
}
}
}
else
{
lean_object* v_ks_1545_; lean_object* v_vs_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_ks_1545_ = lean_ctor_get(v_x_1520_, 0);
lean_inc_ref(v_ks_1545_);
v_vs_1546_ = lean_ctor_get(v_x_1520_, 1);
lean_inc_ref(v_vs_1546_);
lean_dec_ref(v_x_1520_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_ks_1545_, v_vs_1546_, v___x_1547_, v_x_1522_);
lean_dec_ref(v_vs_1546_);
lean_dec_ref(v_ks_1545_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___boxed(lean_object* v_x_1549_, lean_object* v_x_1550_, lean_object* v_x_1551_){
_start:
{
size_t v_x_18765__boxed_1552_; lean_object* v_res_1553_; 
v_x_18765__boxed_1552_ = lean_unbox_usize(v_x_1550_);
lean_dec(v_x_1550_);
v_res_1553_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1549_, v_x_18765__boxed_1552_, v_x_1551_);
lean_dec(v_x_1551_);
return v_res_1553_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1554_; uint64_t v___x_1555_; 
v___x_1554_ = lean_unsigned_to_nat(1723u);
v___x_1555_ = lean_uint64_of_nat(v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(lean_object* v_x_1556_, lean_object* v_x_1557_){
_start:
{
uint64_t v___y_1559_; 
if (lean_obj_tag(v_x_1557_) == 0)
{
uint64_t v___x_1562_; 
v___x_1562_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0);
v___y_1559_ = v___x_1562_;
goto v___jp_1558_;
}
else
{
uint64_t v_hash_1563_; 
v_hash_1563_ = lean_ctor_get_uint64(v_x_1557_, sizeof(void*)*2);
v___y_1559_ = v_hash_1563_;
goto v___jp_1558_;
}
v___jp_1558_:
{
size_t v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_uint64_to_usize(v___y_1559_);
v___x_1561_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1556_, v___x_1560_, v_x_1557_);
return v___x_1561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___boxed(lean_object* v_x_1564_, lean_object* v_x_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1564_, v_x_1565_);
lean_dec(v_x_1565_);
return v_res_1566_;
}
}
static lean_object* _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(lean_object* v___x_1570_, uint8_t v___x_1571_, lean_object* v___x_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
if (lean_obj_tag(v_a_1573_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref(v___x_1572_);
lean_dec_ref(v___x_1570_);
v___x_1575_ = lean_array_to_list(v_a_1574_);
return v___x_1575_;
}
else
{
lean_object* v_head_1576_; lean_object* v_tail_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1617_; 
v_head_1576_ = lean_ctor_get(v_a_1573_, 0);
v_tail_1577_ = lean_ctor_get(v_a_1573_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_a_1573_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1579_ = v_a_1573_;
v_isShared_1580_ = v_isSharedCheck_1617_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_tail_1577_);
lean_inc(v_head_1576_);
lean_dec(v_a_1573_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1617_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_fst_1581_; lean_object* v_snd_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1616_; 
v_fst_1581_ = lean_ctor_get(v_head_1576_, 0);
v_snd_1582_ = lean_ctor_get(v_head_1576_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_head_1576_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1584_ = v_head_1576_;
v_isShared_1585_ = v_isSharedCheck_1616_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_snd_1582_);
lean_inc(v_fst_1581_);
lean_dec(v_head_1576_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1616_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___y_1587_; lean_object* v___y_1602_; uint8_t v___y_1603_; lean_object* v_unfoldAxiomCounter_1605_; lean_object* v___x_1606_; lean_object* v___y_1608_; lean_object* v___x_1614_; 
v_unfoldAxiomCounter_1605_ = lean_ctor_get(v___x_1570_, 1);
v___x_1606_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_unfoldAxiomCounter_1605_);
v___x_1614_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_unfoldAxiomCounter_1605_, v_fst_1581_);
if (lean_obj_tag(v___x_1614_) == 0)
{
v___y_1608_ = v___x_1606_;
goto v___jp_1607_;
}
else
{
lean_object* v_val_1615_; 
v_val_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1615_);
lean_dec_ref(v___x_1614_);
v___y_1608_ = v_val_1615_;
goto v___jp_1607_;
}
v___jp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1588_ = l_Lean_MessageData_ofConstName(v_fst_1581_, v___x_1571_);
v___x_1589_ = lean_obj_once(&l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1, &l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1_once, _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1);
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 7);
lean_ctor_set(v___x_1584_, 1, v___x_1589_);
lean_ctor_set(v___x_1584_, 0, v___x_1588_);
v___x_1591_ = v___x_1584_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1592_ = l_Nat_reprFast(v___y_1587_);
v___x_1593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
v___x_1594_ = l_Lean_MessageData_ofFormat(v___x_1593_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 7);
lean_ctor_set(v___x_1579_, 1, v___x_1594_);
lean_ctor_set(v___x_1579_, 0, v___x_1591_);
v___x_1596_ = v___x_1579_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_array_push(v_a_1574_, v___x_1596_);
v_a_1573_ = v_tail_1577_;
v_a_1574_ = v___x_1597_;
goto _start;
}
}
}
v___jp_1601_:
{
if (v___y_1603_ == 0)
{
lean_dec(v___y_1602_);
lean_del_object(v___x_1584_);
lean_dec(v_fst_1581_);
lean_del_object(v___x_1579_);
v_a_1573_ = v_tail_1577_;
goto _start;
}
else
{
v___y_1587_ = v___y_1602_;
goto v___jp_1586_;
}
}
v___jp_1607_:
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = lean_nat_sub(v_snd_1582_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec(v_snd_1582_);
v___x_1610_ = lean_nat_dec_lt(v___x_1606_, v___x_1609_);
if (v___x_1610_ == 0)
{
v___y_1602_ = v___x_1609_;
v___y_1603_ = v___x_1610_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1611_; 
lean_inc(v_fst_1581_);
lean_inc_ref(v___x_1572_);
v___x_1611_ = l_Lean_getOriginalConstKind_x3f(v___x_1572_, v_fst_1581_);
if (lean_obj_tag(v___x_1611_) == 1)
{
lean_object* v_val_1612_; uint8_t v___x_1613_; 
v_val_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_val_1612_);
lean_dec_ref(v___x_1611_);
v___x_1613_ = lean_unbox(v_val_1612_);
lean_dec(v_val_1612_);
if (v___x_1613_ == 0)
{
v___y_1587_ = v___x_1609_;
goto v___jp_1586_;
}
else
{
v___y_1602_ = v___x_1609_;
v___y_1603_ = v___x_1571_;
goto v___jp_1601_;
}
}
else
{
lean_dec(v___x_1611_);
v___y_1602_ = v___x_1609_;
v___y_1603_ = v___x_1571_;
goto v___jp_1601_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___boxed(lean_object* v___x_1618_, lean_object* v___x_1619_, lean_object* v___x_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v___x_18858__boxed_1623_; lean_object* v_res_1624_; 
v___x_18858__boxed_1623_ = lean_unbox(v___x_1619_);
v_res_1624_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v___x_1618_, v___x_18858__boxed_1623_, v___x_1620_, v_a_1621_, v_a_1622_);
return v_res_1624_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__0));
v___x_1627_ = l_Lean_stringToMessageData(v___x_1626_);
return v___x_1627_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__2));
v___x_1630_ = l_Lean_stringToMessageData(v___x_1629_);
return v___x_1630_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__4));
v___x_1633_ = l_Lean_stringToMessageData(v___x_1632_);
return v___x_1633_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__6));
v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__8));
v___x_1639_ = l_Lean_stringToMessageData(v___x_1638_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__11));
v___x_1644_ = l_Lean_stringToMessageData(v___x_1643_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_box(1);
v___x_1646_ = l_Lean_MessageData_ofFormat(v___x_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__14));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object* v_type_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_inc_ref(v_type_1650_);
v___x_1656_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed), 6, 1);
lean_closure_set(v___x_1656_, 0, v_type_1650_);
v___x_1657_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_type_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1828_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1828_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1828_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v_env_1663_; lean_object* v___x_1664_; uint8_t v_isModule_1665_; 
v___x_1662_ = lean_st_ref_get(v_a_1654_);
v_env_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc_ref(v_env_1663_);
lean_dec(v___x_1662_);
v___x_1664_ = l_Lean_Environment_header(v_env_1663_);
lean_dec_ref(v_env_1663_);
v_isModule_1665_ = lean_ctor_get_uint8(v___x_1664_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1664_);
if (v_isModule_1665_ == 0)
{
lean_object* v___x_1667_; 
lean_dec_ref(v___x_1656_);
lean_dec_ref(v_a_1653_);
if (v_isShared_1661_ == 0)
{
v___x_1667_ = v___x_1660_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1658_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
else
{
lean_object* v___x_1669_; 
lean_del_object(v___x_1660_);
lean_inc_ref(v___x_1656_);
v___x_1669_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1656_, v_isModule_1665_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1814_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1814_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1814_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
uint8_t v___x_1674_; 
v___x_1674_ = lean_expr_eqv(v_a_1658_, v_a_1670_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v_diag_1677_; lean_object* v_fileName_1678_; lean_object* v_fileMap_1679_; lean_object* v_options_1680_; lean_object* v_currRecDepth_1681_; lean_object* v_ref_1682_; lean_object* v_currNamespace_1683_; lean_object* v_openDecls_1684_; lean_object* v_initHeartbeats_1685_; lean_object* v_maxHeartbeats_1686_; lean_object* v_quotContext_1687_; lean_object* v_currMacroScope_1688_; lean_object* v_cancelTk_x3f_1689_; uint8_t v_suppressElabErrors_1690_; lean_object* v_inheritedTraceOptions_1691_; lean_object* v_env_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v_a_1707_; lean_object* v___y_1753_; uint8_t v___y_1754_; uint8_t v___x_1765_; lean_object* v_fileName_1767_; lean_object* v_fileMap_1768_; lean_object* v_currRecDepth_1769_; lean_object* v_ref_1770_; lean_object* v_currNamespace_1771_; lean_object* v_openDecls_1772_; lean_object* v_initHeartbeats_1773_; lean_object* v_maxHeartbeats_1774_; lean_object* v_quotContext_1775_; lean_object* v_currMacroScope_1776_; lean_object* v_cancelTk_x3f_1777_; uint8_t v_suppressElabErrors_1778_; lean_object* v_inheritedTraceOptions_1779_; lean_object* v___y_1780_; uint8_t v___y_1789_; uint8_t v___x_1810_; 
lean_del_object(v___x_1672_);
v___x_1675_ = lean_st_ref_get(v_a_1652_);
v___x_1676_ = lean_st_ref_get(v_a_1654_);
v_diag_1677_ = lean_ctor_get(v___x_1675_, 4);
lean_inc_ref(v_diag_1677_);
lean_dec(v___x_1675_);
v_fileName_1678_ = lean_ctor_get(v_a_1653_, 0);
v_fileMap_1679_ = lean_ctor_get(v_a_1653_, 1);
v_options_1680_ = lean_ctor_get(v_a_1653_, 2);
v_currRecDepth_1681_ = lean_ctor_get(v_a_1653_, 3);
v_ref_1682_ = lean_ctor_get(v_a_1653_, 5);
v_currNamespace_1683_ = lean_ctor_get(v_a_1653_, 6);
v_openDecls_1684_ = lean_ctor_get(v_a_1653_, 7);
v_initHeartbeats_1685_ = lean_ctor_get(v_a_1653_, 8);
v_maxHeartbeats_1686_ = lean_ctor_get(v_a_1653_, 9);
v_quotContext_1687_ = lean_ctor_get(v_a_1653_, 10);
v_currMacroScope_1688_ = lean_ctor_get(v_a_1653_, 11);
v_cancelTk_x3f_1689_ = lean_ctor_get(v_a_1653_, 12);
v_suppressElabErrors_1690_ = lean_ctor_get_uint8(v_a_1653_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1691_ = lean_ctor_get(v_a_1653_, 13);
v_env_1692_ = lean_ctor_get(v___x_1676_, 0);
lean_inc_ref(v_env_1692_);
lean_dec(v___x_1676_);
v___x_1693_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1680_);
v___x_1694_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(v_options_1680_, v___x_1693_, v_isModule_1665_);
v___x_1695_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__1, &l_Lean_Compiler_LCNF_toLCNFType___closed__1_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1);
v___x_1696_ = l_Lean_MessageData_ofExpr(v_a_1658_);
v___x_1697_ = l_Lean_indentD(v___x_1696_);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1695_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__3, &l_Lean_Compiler_LCNF_toLCNFType___closed__3_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = l_Lean_MessageData_ofExpr(v_a_1670_);
v___x_1702_ = l_Lean_indentD(v___x_1701_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1700_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__5, &l_Lean_Compiler_LCNF_toLCNFType___closed__5_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1765_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v___x_1694_, v___x_1693_);
v___x_1810_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1692_);
lean_dec_ref(v_env_1692_);
if (v___x_1810_ == 0)
{
if (v___x_1765_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1691_);
lean_inc(v_cancelTk_x3f_1689_);
lean_inc(v_currMacroScope_1688_);
lean_inc(v_quotContext_1687_);
lean_inc(v_maxHeartbeats_1686_);
lean_inc(v_initHeartbeats_1685_);
lean_inc(v_openDecls_1684_);
lean_inc(v_currNamespace_1683_);
lean_inc(v_ref_1682_);
lean_inc(v_currRecDepth_1681_);
lean_inc_ref(v_fileMap_1679_);
lean_inc_ref(v_fileName_1678_);
v_fileName_1767_ = v_fileName_1678_;
v_fileMap_1768_ = v_fileMap_1679_;
v_currRecDepth_1769_ = v_currRecDepth_1681_;
v_ref_1770_ = v_ref_1682_;
v_currNamespace_1771_ = v_currNamespace_1683_;
v_openDecls_1772_ = v_openDecls_1684_;
v_initHeartbeats_1773_ = v_initHeartbeats_1685_;
v_maxHeartbeats_1774_ = v_maxHeartbeats_1686_;
v_quotContext_1775_ = v_quotContext_1687_;
v_currMacroScope_1776_ = v_currMacroScope_1688_;
v_cancelTk_x3f_1777_ = v_cancelTk_x3f_1689_;
v_suppressElabErrors_1778_ = v_suppressElabErrors_1690_;
v_inheritedTraceOptions_1779_ = v_inheritedTraceOptions_1691_;
v___y_1780_ = v_a_1654_;
goto v___jp_1766_;
}
else
{
v___y_1789_ = v___x_1810_;
goto v___jp_1788_;
}
}
else
{
v___y_1789_ = v___x_1765_;
goto v___jp_1788_;
}
v___jp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v_snd_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1729_; 
lean_inc_ref(v_a_1707_);
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v_a_1707_);
v___x_1709_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1652_, v_diag_1677_, v___x_1708_);
lean_dec_ref(v___x_1708_);
lean_dec_ref(v___x_1709_);
v_snd_1710_ = lean_ctor_get(v_a_1707_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_a_1707_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v_a_1707_, 0);
lean_dec(v_unused_1730_);
v___x_1712_ = v_a_1707_;
v_isShared_1713_ = v_isSharedCheck_1729_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snd_1710_);
lean_dec(v_a_1707_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1729_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1714_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__7, &l_Lean_Compiler_LCNF_toLCNFType___closed__7_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7);
if (v_isShared_1713_ == 0)
{
lean_ctor_set_tag(v___x_1712_, 7);
lean_ctor_set(v___x_1712_, 0, v___x_1714_);
v___x_1716_ = v___x_1712_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_snd_1710_);
v___x_1716_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v___x_1717_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__9, &l_Lean_Compiler_LCNF_toLCNFType___closed__9_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9);
v___x_1718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1716_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_1718_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec_ref(v_a_1653_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
v___jp_1731_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v_diag_1734_; lean_object* v_env_1735_; lean_object* v_unfoldAxiomCounter_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1732_ = lean_st_ref_get(v_a_1654_);
v___x_1733_ = lean_st_ref_get(v_a_1652_);
v_diag_1734_ = lean_ctor_get(v___x_1733_, 4);
lean_inc_ref(v_diag_1734_);
lean_dec(v___x_1733_);
v_env_1735_ = lean_ctor_get(v___x_1732_, 0);
lean_inc_ref(v_env_1735_);
lean_dec(v___x_1732_);
v_unfoldAxiomCounter_1736_ = lean_ctor_get(v_diag_1734_, 1);
lean_inc_ref(v_unfoldAxiomCounter_1736_);
lean_dec_ref(v_diag_1734_);
v___x_1737_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_unfoldAxiomCounter_1736_);
lean_dec_ref(v_unfoldAxiomCounter_1736_);
v___x_1738_ = ((lean_object*)(l_Lean_Compiler_LCNF_toLCNFType___closed__10));
lean_inc_ref(v_diag_1677_);
v___x_1739_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(v_diag_1677_, v___x_1674_, v_env_1735_, v___x_1737_, v___x_1738_);
v___x_1740_ = l_List_isEmpty___redArg(v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec_ref(v___x_1705_);
v___x_1741_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__12, &l_Lean_Compiler_LCNF_toLCNFType___closed__12_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12);
v___x_1742_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__13, &l_Lean_Compiler_LCNF_toLCNFType___closed__13_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13);
v___x_1743_ = l_Lean_MessageData_joinSep(v___x_1739_, v___x_1742_);
v___x_1744_ = l_Lean_indentD(v___x_1743_);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1741_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = lean_obj_once(&l_Lean_Compiler_LCNF_toLCNFType___closed__15, &l_Lean_Compiler_LCNF_toLCNFType___closed__15_once, _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15);
v___x_1747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_box(0);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
lean_ctor_set(v___x_1749_, 1, v___x_1747_);
v_a_1707_ = v___x_1749_;
goto v___jp_1706_;
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v___x_1739_);
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v___x_1705_);
v_a_1707_ = v___x_1751_;
goto v___jp_1706_;
}
}
v___jp_1752_:
{
if (v___y_1754_ == 0)
{
lean_dec_ref(v___y_1753_);
goto v___jp_1731_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref(v___x_1705_);
lean_dec_ref(v_a_1653_);
v___x_1755_ = lean_box(0);
v___x_1756_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_1652_, v_diag_1677_, v___x_1755_);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v___x_1756_, 0);
lean_dec(v_unused_1764_);
v___x_1758_ = v___x_1756_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_dec(v___x_1756_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set_tag(v___x_1758_, 1);
lean_ctor_set(v___x_1758_, 0, v___y_1753_);
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___y_1753_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
v___jp_1766_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1781_ = l_Lean_maxRecDepth;
v___x_1782_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(v___x_1694_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1783_, 0, v_fileName_1767_);
lean_ctor_set(v___x_1783_, 1, v_fileMap_1768_);
lean_ctor_set(v___x_1783_, 2, v___x_1694_);
lean_ctor_set(v___x_1783_, 3, v_currRecDepth_1769_);
lean_ctor_set(v___x_1783_, 4, v___x_1782_);
lean_ctor_set(v___x_1783_, 5, v_ref_1770_);
lean_ctor_set(v___x_1783_, 6, v_currNamespace_1771_);
lean_ctor_set(v___x_1783_, 7, v_openDecls_1772_);
lean_ctor_set(v___x_1783_, 8, v_initHeartbeats_1773_);
lean_ctor_set(v___x_1783_, 9, v_maxHeartbeats_1774_);
lean_ctor_set(v___x_1783_, 10, v_quotContext_1775_);
lean_ctor_set(v___x_1783_, 11, v_currMacroScope_1776_);
lean_ctor_set(v___x_1783_, 12, v_cancelTk_x3f_1777_);
lean_ctor_set(v___x_1783_, 13, v_inheritedTraceOptions_1779_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*14, v___x_1765_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*14 + 1, v_suppressElabErrors_1778_);
v___x_1784_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_1656_, v_isModule_1665_, v_a_1651_, v_a_1652_, v___x_1783_, v___y_1780_);
lean_dec_ref(v___x_1783_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_dec_ref(v___x_1784_);
goto v___jp_1731_;
}
else
{
lean_object* v_a_1785_; uint8_t v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v___x_1784_);
v___x_1786_ = l_Lean_Exception_isInterrupt(v_a_1785_);
if (v___x_1786_ == 0)
{
uint8_t v___x_1787_; 
lean_inc(v_a_1785_);
v___x_1787_ = l_Lean_Exception_isRuntime(v_a_1785_);
v___y_1753_ = v_a_1785_;
v___y_1754_ = v___x_1787_;
goto v___jp_1752_;
}
else
{
v___y_1753_ = v_a_1785_;
v___y_1754_ = v___x_1786_;
goto v___jp_1752_;
}
}
}
v___jp_1788_:
{
if (v___y_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v_env_1791_; lean_object* v_nextMacroScope_1792_; lean_object* v_ngen_1793_; lean_object* v_auxDeclNGen_1794_; lean_object* v_traceState_1795_; lean_object* v_messages_1796_; lean_object* v_infoState_1797_; lean_object* v_snapshotTasks_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1808_; 
v___x_1790_ = lean_st_ref_take(v_a_1654_);
v_env_1791_ = lean_ctor_get(v___x_1790_, 0);
v_nextMacroScope_1792_ = lean_ctor_get(v___x_1790_, 1);
v_ngen_1793_ = lean_ctor_get(v___x_1790_, 2);
v_auxDeclNGen_1794_ = lean_ctor_get(v___x_1790_, 3);
v_traceState_1795_ = lean_ctor_get(v___x_1790_, 4);
v_messages_1796_ = lean_ctor_get(v___x_1790_, 6);
v_infoState_1797_ = lean_ctor_get(v___x_1790_, 7);
v_snapshotTasks_1798_ = lean_ctor_get(v___x_1790_, 8);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v___x_1790_, 5);
lean_dec(v_unused_1809_);
v___x_1800_ = v___x_1790_;
v_isShared_1801_ = v_isSharedCheck_1808_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snapshotTasks_1798_);
lean_inc(v_infoState_1797_);
lean_inc(v_messages_1796_);
lean_inc(v_traceState_1795_);
lean_inc(v_auxDeclNGen_1794_);
lean_inc(v_ngen_1793_);
lean_inc(v_nextMacroScope_1792_);
lean_inc(v_env_1791_);
lean_dec(v___x_1790_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1808_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1802_ = l_Lean_Kernel_enableDiag(v_env_1791_, v___x_1765_);
v___x_1803_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 5, v___x_1803_);
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_nextMacroScope_1792_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_ngen_1793_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_auxDeclNGen_1794_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_traceState_1795_);
lean_ctor_set(v_reuseFailAlloc_1807_, 5, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1807_, 6, v_messages_1796_);
lean_ctor_set(v_reuseFailAlloc_1807_, 7, v_infoState_1797_);
lean_ctor_set(v_reuseFailAlloc_1807_, 8, v_snapshotTasks_1798_);
v___x_1805_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_st_ref_set(v_a_1654_, v___x_1805_);
lean_inc_ref(v_inheritedTraceOptions_1691_);
lean_inc(v_cancelTk_x3f_1689_);
lean_inc(v_currMacroScope_1688_);
lean_inc(v_quotContext_1687_);
lean_inc(v_maxHeartbeats_1686_);
lean_inc(v_initHeartbeats_1685_);
lean_inc(v_openDecls_1684_);
lean_inc(v_currNamespace_1683_);
lean_inc(v_ref_1682_);
lean_inc(v_currRecDepth_1681_);
lean_inc_ref(v_fileMap_1679_);
lean_inc_ref(v_fileName_1678_);
v_fileName_1767_ = v_fileName_1678_;
v_fileMap_1768_ = v_fileMap_1679_;
v_currRecDepth_1769_ = v_currRecDepth_1681_;
v_ref_1770_ = v_ref_1682_;
v_currNamespace_1771_ = v_currNamespace_1683_;
v_openDecls_1772_ = v_openDecls_1684_;
v_initHeartbeats_1773_ = v_initHeartbeats_1685_;
v_maxHeartbeats_1774_ = v_maxHeartbeats_1686_;
v_quotContext_1775_ = v_quotContext_1687_;
v_currMacroScope_1776_ = v_currMacroScope_1688_;
v_cancelTk_x3f_1777_ = v_cancelTk_x3f_1689_;
v_suppressElabErrors_1778_ = v_suppressElabErrors_1690_;
v_inheritedTraceOptions_1779_ = v_inheritedTraceOptions_1691_;
v___y_1780_ = v_a_1654_;
goto v___jp_1766_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1691_);
lean_inc(v_cancelTk_x3f_1689_);
lean_inc(v_currMacroScope_1688_);
lean_inc(v_quotContext_1687_);
lean_inc(v_maxHeartbeats_1686_);
lean_inc(v_initHeartbeats_1685_);
lean_inc(v_openDecls_1684_);
lean_inc(v_currNamespace_1683_);
lean_inc(v_ref_1682_);
lean_inc(v_currRecDepth_1681_);
lean_inc_ref(v_fileMap_1679_);
lean_inc_ref(v_fileName_1678_);
v_fileName_1767_ = v_fileName_1678_;
v_fileMap_1768_ = v_fileMap_1679_;
v_currRecDepth_1769_ = v_currRecDepth_1681_;
v_ref_1770_ = v_ref_1682_;
v_currNamespace_1771_ = v_currNamespace_1683_;
v_openDecls_1772_ = v_openDecls_1684_;
v_initHeartbeats_1773_ = v_initHeartbeats_1685_;
v_maxHeartbeats_1774_ = v_maxHeartbeats_1686_;
v_quotContext_1775_ = v_quotContext_1687_;
v_currMacroScope_1776_ = v_currMacroScope_1688_;
v_cancelTk_x3f_1777_ = v_cancelTk_x3f_1689_;
v_suppressElabErrors_1778_ = v_suppressElabErrors_1690_;
v_inheritedTraceOptions_1779_ = v_inheritedTraceOptions_1691_;
v___y_1780_ = v_a_1654_;
goto v___jp_1766_;
}
}
}
else
{
lean_object* v___x_1812_; 
lean_dec(v_a_1670_);
lean_dec_ref(v___x_1656_);
lean_dec_ref(v_a_1653_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v_a_1658_);
v___x_1812_ = v___x_1672_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1658_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
lean_object* v_a_1815_; uint8_t v___y_1817_; uint8_t v___x_1826_; 
lean_dec_ref(v___x_1656_);
lean_dec_ref(v_a_1653_);
v_a_1815_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1815_);
v___x_1826_ = l_Lean_Exception_isInterrupt(v_a_1815_);
if (v___x_1826_ == 0)
{
uint8_t v___x_1827_; 
v___x_1827_ = l_Lean_Exception_isRuntime(v_a_1815_);
v___y_1817_ = v___x_1827_;
goto v___jp_1816_;
}
else
{
lean_dec(v_a_1815_);
v___y_1817_ = v___x_1826_;
goto v___jp_1816_;
}
v___jp_1816_:
{
if (v___y_1817_ == 0)
{
lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v___x_1669_, 0);
lean_dec(v_unused_1825_);
v___x_1819_ = v___x_1669_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_dec(v___x_1669_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 0);
lean_ctor_set(v___x_1819_, 0, v_a_1658_);
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1658_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
lean_dec(v_a_1658_);
return v___x_1669_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1656_);
lean_dec_ref(v_a_1653_);
return v___x_1657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toLCNFType___boxed(lean_object* v_type_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Compiler_LCNF_toLCNFType(v_type_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(lean_object* v_00_u03b2_1836_, lean_object* v_x_1837_, lean_object* v_x_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_x_1837_, v_x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___boxed(lean_object* v_00_u03b2_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(v_00_u03b2_1840_, v_x_1841_, v_x_1842_);
lean_dec(v_x_1842_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(lean_object* v_00_u03b2_1844_, lean_object* v_m_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_m_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___boxed(lean_object* v_00_u03b2_1847_, lean_object* v_m_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(v_00_u03b2_1847_, v_m_1848_);
lean_dec_ref(v_m_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(lean_object* v_00_u03b2_1850_, lean_object* v_x_1851_, size_t v_x_1852_, lean_object* v_x_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_1851_, v_x_1852_, v_x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_, lean_object* v_x_1858_){
_start:
{
size_t v_x_19320__boxed_1859_; lean_object* v_res_1860_; 
v_x_19320__boxed_1859_ = lean_unbox_usize(v_x_1857_);
lean_dec(v_x_1857_);
v_res_1860_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(v_00_u03b2_1855_, v_x_1856_, v_x_19320__boxed_1859_, v_x_1858_);
lean_dec(v_x_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(lean_object* v_00_u03c3_1861_, lean_object* v_00_u03b2_1862_, lean_object* v_map_1863_, lean_object* v_f_1864_, lean_object* v_init_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_1863_, v_f_1864_, v_init_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1867_, lean_object* v_00_u03b2_1868_, lean_object* v_map_1869_, lean_object* v_f_1870_, lean_object* v_init_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(v_00_u03c3_1867_, v_00_u03b2_1868_, v_map_1869_, v_f_1870_, v_init_1871_);
lean_dec_ref(v_map_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1873_, lean_object* v_keys_1874_, lean_object* v_vals_1875_, lean_object* v_heq_1876_, lean_object* v_i_1877_, lean_object* v_k_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_keys_1874_, v_vals_1875_, v_i_1877_, v_k_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1880_, lean_object* v_keys_1881_, lean_object* v_vals_1882_, lean_object* v_heq_1883_, lean_object* v_i_1884_, lean_object* v_k_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(v_00_u03b2_1880_, v_keys_1881_, v_vals_1882_, v_heq_1883_, v_i_1884_, v_k_1885_);
lean_dec(v_k_1885_);
lean_dec_ref(v_vals_1882_);
lean_dec_ref(v_keys_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(lean_object* v_map_1887_, lean_object* v_f_1888_, lean_object* v_init_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1888_, v_map_1887_, v_init_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_map_1891_, lean_object* v_f_1892_, lean_object* v_init_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(v_map_1891_, v_f_1892_, v_init_1893_);
lean_dec_ref(v_map_1891_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(lean_object* v_00_u03c3_1895_, lean_object* v_00_u03b2_1896_, lean_object* v_map_1897_, lean_object* v_f_1898_, lean_object* v_init_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1898_, v_map_1897_, v_init_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03c3_1901_, lean_object* v_00_u03b2_1902_, lean_object* v_map_1903_, lean_object* v_f_1904_, lean_object* v_init_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(v_00_u03c3_1901_, v_00_u03b2_1902_, v_map_1903_, v_f_1904_, v_init_1905_);
lean_dec_ref(v_map_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(lean_object* v_00_u03c3_1907_, lean_object* v_00_u03b1_1908_, lean_object* v_00_u03b2_1909_, lean_object* v_f_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_1910_, v_x_1911_, v_x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03c3_1914_, lean_object* v_00_u03b1_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_f_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(v_00_u03c3_1914_, v_00_u03b1_1915_, v_00_u03b2_1916_, v_f_1917_, v_x_1918_, v_x_1919_);
lean_dec_ref(v_x_1918_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(lean_object* v_00_u03b1_1921_, lean_object* v_00_u03b2_1922_, lean_object* v_00_u03c3_1923_, lean_object* v_f_1924_, lean_object* v_as_1925_, size_t v_i_1926_, size_t v_stop_1927_, lean_object* v_b_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_1924_, v_as_1925_, v_i_1926_, v_stop_1927_, v_b_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___boxed(lean_object* v_00_u03b1_1930_, lean_object* v_00_u03b2_1931_, lean_object* v_00_u03c3_1932_, lean_object* v_f_1933_, lean_object* v_as_1934_, lean_object* v_i_1935_, lean_object* v_stop_1936_, lean_object* v_b_1937_){
_start:
{
size_t v_i_boxed_1938_; size_t v_stop_boxed_1939_; lean_object* v_res_1940_; 
v_i_boxed_1938_ = lean_unbox_usize(v_i_1935_);
lean_dec(v_i_1935_);
v_stop_boxed_1939_ = lean_unbox_usize(v_stop_1936_);
lean_dec(v_stop_1936_);
v_res_1940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(v_00_u03b1_1930_, v_00_u03b2_1931_, v_00_u03c3_1932_, v_f_1933_, v_as_1934_, v_i_boxed_1938_, v_stop_boxed_1939_, v_b_1937_);
lean_dec_ref(v_as_1934_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(lean_object* v_00_u03c3_1941_, lean_object* v_00_u03b1_1942_, lean_object* v_00_u03b2_1943_, lean_object* v_f_1944_, lean_object* v_keys_1945_, lean_object* v_vals_1946_, lean_object* v_heq_1947_, lean_object* v_i_1948_, lean_object* v_acc_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_1944_, v_keys_1945_, v_vals_1946_, v_i_1948_, v_acc_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___boxed(lean_object* v_00_u03c3_1951_, lean_object* v_00_u03b1_1952_, lean_object* v_00_u03b2_1953_, lean_object* v_f_1954_, lean_object* v_keys_1955_, lean_object* v_vals_1956_, lean_object* v_heq_1957_, lean_object* v_i_1958_, lean_object* v_acc_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(v_00_u03c3_1951_, v_00_u03b1_1952_, v_00_u03b2_1953_, v_f_1954_, v_keys_1955_, v_vals_1956_, v_heq_1957_, v_i_1958_, v_acc_1959_);
lean_dec_ref(v_vals_1956_);
lean_dec_ref(v_keys_1955_);
return v_res_1960_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1(void){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = l_Lean_Compiler_LCNF_erasedExpr;
v___x_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes_x3f(lean_object* v_a_1965_, lean_object* v_b_1966_){
_start:
{
lean_object* v___y_1970_; uint8_t v___y_1973_; uint8_t v___x_2046_; 
v___x_2046_ = l_Lean_Expr_isErased(v_a_1965_);
if (v___x_2046_ == 0)
{
uint8_t v___x_2047_; 
v___x_2047_ = l_Lean_Expr_isErased(v_b_1966_);
v___y_1973_ = v___x_2047_;
goto v___jp_1972_;
}
else
{
v___y_1973_ = v___x_2046_;
goto v___jp_1972_;
}
v___jp_1967_:
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1968_;
}
v___jp_1969_:
{
if (lean_obj_tag(v___y_1970_) == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_1971_;
}
else
{
return v___y_1970_;
}
}
v___jp_1972_:
{
if (v___y_1973_ == 0)
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_expr_eqv(v_a_1965_, v_b_1966_);
if (v___x_1974_ == 0)
{
lean_object* v_a_x27_1975_; lean_object* v_b_x27_1976_; uint8_t v___x_1977_; 
lean_inc_ref(v_a_1965_);
v_a_x27_1975_ = l_Lean_Expr_headBeta(v_a_1965_);
lean_inc_ref(v_b_1966_);
v_b_x27_1976_ = l_Lean_Expr_headBeta(v_b_1966_);
v___x_1977_ = lean_expr_eqv(v_a_1965_, v_a_x27_1975_);
if (v___x_1977_ == 0)
{
lean_dec_ref(v_b_1966_);
lean_dec_ref(v_a_1965_);
v_a_1965_ = v_a_x27_1975_;
v_b_1966_ = v_b_x27_1976_;
goto _start;
}
else
{
if (v___x_1974_ == 0)
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_expr_eqv(v_b_1966_, v_b_x27_1976_);
if (v___x_1979_ == 0)
{
lean_dec_ref(v_b_1966_);
lean_dec_ref(v_a_1965_);
v_a_1965_ = v_a_x27_1975_;
v_b_1966_ = v_b_x27_1976_;
goto _start;
}
else
{
lean_dec_ref(v_b_x27_1976_);
lean_dec_ref(v_a_x27_1975_);
switch(lean_obj_tag(v_a_1965_))
{
case 10:
{
lean_object* v_expr_1981_; 
v_expr_1981_ = lean_ctor_get(v_a_1965_, 1);
lean_inc_ref(v_expr_1981_);
lean_dec_ref(v_a_1965_);
v_a_1965_ = v_expr_1981_;
goto _start;
}
case 5:
{
switch(lean_obj_tag(v_b_1966_))
{
case 10:
{
lean_object* v_expr_1983_; 
v_expr_1983_ = lean_ctor_get(v_b_1966_, 1);
lean_inc_ref(v_expr_1983_);
lean_dec_ref(v_b_1966_);
v_b_1966_ = v_expr_1983_;
goto _start;
}
case 5:
{
lean_object* v_fn_1985_; lean_object* v_arg_1986_; lean_object* v_fn_1987_; lean_object* v_arg_1988_; lean_object* v___x_1989_; 
v_fn_1985_ = lean_ctor_get(v_a_1965_, 0);
lean_inc_ref(v_fn_1985_);
v_arg_1986_ = lean_ctor_get(v_a_1965_, 1);
lean_inc_ref(v_arg_1986_);
lean_dec_ref(v_a_1965_);
v_fn_1987_ = lean_ctor_get(v_b_1966_, 0);
lean_inc_ref(v_fn_1987_);
v_arg_1988_ = lean_ctor_get(v_b_1966_, 1);
lean_inc_ref(v_arg_1988_);
lean_dec_ref(v_b_1966_);
v___x_1989_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_fn_1985_, v_fn_1987_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1986_);
v___y_1970_ = v___x_1989_;
goto v___jp_1969_;
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1991_; 
v_val_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_val_1990_);
lean_dec_ref(v___x_1989_);
v___x_1991_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_arg_1986_, v_arg_1988_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_dec(v_val_1990_);
v___y_1970_ = v___x_1991_;
goto v___jp_1969_;
}
else
{
lean_object* v_val_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2000_; 
v_val_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_val_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1996_ = l_Lean_Expr_app___override(v_val_1990_, v_val_1992_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_1996_);
v___x_1998_ = v___x_1994_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
default: 
{
lean_dec_ref(v_a_1965_);
lean_dec_ref(v_b_1966_);
goto v___jp_1967_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_1966_))
{
case 10:
{
lean_object* v_expr_2001_; 
v_expr_2001_ = lean_ctor_get(v_b_1966_, 1);
lean_inc_ref(v_expr_2001_);
lean_dec_ref(v_b_1966_);
v_b_1966_ = v_expr_2001_;
goto _start;
}
case 7:
{
lean_object* v_binderName_2003_; lean_object* v_binderType_2004_; lean_object* v_body_2005_; lean_object* v_binderType_2006_; lean_object* v_body_2007_; lean_object* v___x_2008_; 
v_binderName_2003_ = lean_ctor_get(v_a_1965_, 0);
lean_inc(v_binderName_2003_);
v_binderType_2004_ = lean_ctor_get(v_a_1965_, 1);
lean_inc_ref(v_binderType_2004_);
v_body_2005_ = lean_ctor_get(v_a_1965_, 2);
lean_inc_ref(v_body_2005_);
lean_dec_ref(v_a_1965_);
v_binderType_2006_ = lean_ctor_get(v_b_1966_, 1);
lean_inc_ref(v_binderType_2006_);
v_body_2007_ = lean_ctor_get(v_b_1966_, 2);
lean_inc_ref(v_body_2007_);
lean_dec_ref(v_b_1966_);
v___x_2008_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_2004_, v_binderType_2006_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_dec_ref(v_body_2007_);
lean_dec_ref(v_body_2005_);
lean_dec(v_binderName_2003_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_2009_;
}
else
{
return v___x_2008_;
}
}
else
{
lean_object* v_val_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2020_; 
v_val_2010_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2012_ = v___x_2008_;
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_val_2010_);
lean_dec(v___x_2008_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2014_ = l_Lean_Compiler_LCNF_joinTypes(v_body_2005_, v_body_2007_);
v___x_2015_ = 0;
v___x_2016_ = l_Lean_Expr_forallE___override(v_binderName_2003_, v_val_2010_, v___x_2014_, v___x_2015_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2016_);
v___x_2018_ = v___x_2012_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
default: 
{
lean_dec_ref(v_a_1965_);
lean_dec_ref(v_b_1966_);
goto v___jp_1967_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_1966_))
{
case 10:
{
lean_object* v_expr_2021_; 
v_expr_2021_ = lean_ctor_get(v_b_1966_, 1);
lean_inc_ref(v_expr_2021_);
lean_dec_ref(v_b_1966_);
v_b_1966_ = v_expr_2021_;
goto _start;
}
case 6:
{
lean_object* v_binderName_2023_; lean_object* v_binderType_2024_; lean_object* v_body_2025_; lean_object* v_binderType_2026_; lean_object* v_body_2027_; lean_object* v___x_2028_; 
v_binderName_2023_ = lean_ctor_get(v_a_1965_, 0);
lean_inc(v_binderName_2023_);
v_binderType_2024_ = lean_ctor_get(v_a_1965_, 1);
lean_inc_ref(v_binderType_2024_);
v_body_2025_ = lean_ctor_get(v_a_1965_, 2);
lean_inc_ref(v_body_2025_);
lean_dec_ref(v_a_1965_);
v_binderType_2026_ = lean_ctor_get(v_b_1966_, 1);
lean_inc_ref(v_binderType_2026_);
v_body_2027_ = lean_ctor_get(v_b_1966_, 2);
lean_inc_ref(v_body_2027_);
lean_dec_ref(v_b_1966_);
v___x_2028_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_binderType_2024_, v_binderType_2026_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_dec_ref(v_body_2027_);
lean_dec_ref(v_body_2025_);
lean_dec(v_binderName_2023_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v___x_2029_; 
v___x_2029_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
return v___x_2029_;
}
else
{
return v___x_2028_;
}
}
else
{
lean_object* v_val_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2040_; 
v_val_2030_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2032_ = v___x_2028_;
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_val_2030_);
lean_dec(v___x_2028_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2034_ = l_Lean_Compiler_LCNF_joinTypes(v_body_2025_, v_body_2027_);
v___x_2035_ = 0;
v___x_2036_ = l_Lean_Expr_lam___override(v_binderName_2023_, v_val_2030_, v___x_2034_, v___x_2035_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2036_);
v___x_2038_ = v___x_2032_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
default: 
{
lean_dec_ref(v_a_1965_);
lean_dec_ref(v_b_1966_);
goto v___jp_1967_;
}
}
}
default: 
{
if (lean_obj_tag(v_b_1966_) == 10)
{
lean_object* v_expr_2041_; 
v_expr_2041_ = lean_ctor_get(v_b_1966_, 1);
lean_inc_ref(v_expr_2041_);
lean_dec_ref(v_b_1966_);
v_b_1966_ = v_expr_2041_;
goto _start;
}
else
{
lean_dec_ref(v_b_1966_);
lean_dec_ref(v_a_1965_);
goto v___jp_1967_;
}
}
}
}
}
else
{
lean_dec_ref(v_b_1966_);
lean_dec_ref(v_a_1965_);
v_a_1965_ = v_a_x27_1975_;
v_b_1966_ = v_b_x27_1976_;
goto _start;
}
}
}
else
{
lean_object* v___x_2044_; 
lean_dec_ref(v_b_1966_);
v___x_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_a_1965_);
return v___x_2044_;
}
}
else
{
lean_object* v___x_2045_; 
lean_dec_ref(v_b_1966_);
lean_dec_ref(v_a_1965_);
v___x_2045_ = lean_obj_once(&l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1, &l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1);
return v___x_2045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object* v_a_2048_, lean_object* v_b_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_a_2048_, v_b_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_obj_once(&l_Lean_Compiler_LCNF_anyExpr___closed__2, &l_Lean_Compiler_LCNF_anyExpr___closed__2_once, _init_l_Lean_Compiler_LCNF_anyExpr___closed__2);
return v___x_2051_;
}
else
{
lean_object* v_val_2052_; 
v_val_2052_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_val_2052_);
lean_dec_ref(v___x_2050_);
return v_val_2052_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object* v_type_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_Expr_headBeta(v_type_2053_);
switch(lean_obj_tag(v___x_2054_))
{
case 3:
{
uint8_t v___x_2055_; 
lean_dec_ref(v___x_2054_);
v___x_2055_ = 1;
return v___x_2055_;
}
case 7:
{
lean_object* v_body_2056_; 
v_body_2056_ = lean_ctor_get(v___x_2054_, 2);
lean_inc_ref(v_body_2056_);
lean_dec_ref(v___x_2054_);
v_type_2053_ = v_body_2056_;
goto _start;
}
default: 
{
uint8_t v___x_2058_; 
lean_dec_ref(v___x_2054_);
v___x_2058_ = 0;
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTypeFormerType___boxed(lean_object* v_type_2059_){
_start:
{
uint8_t v_res_2060_; lean_object* v_r_2061_; 
v_res_2060_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_2059_);
v_r_2061_ = lean_box(v_res_2060_);
return v_r_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(lean_object* v_msgData_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; lean_object* v_env_2067_; lean_object* v_options_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2066_ = lean_st_ref_get(v___y_2064_);
v_env_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc_ref(v_env_2067_);
lean_dec(v___x_2066_);
v_options_2068_ = lean_ctor_get(v___y_2063_, 2);
v___x_2069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_2070_ = lean_unsigned_to_nat(32u);
v___x_2071_ = lean_mk_empty_array_with_capacity(v___x_2070_);
lean_dec_ref(v___x_2071_);
v___x_2072_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_2068_);
v___x_2073_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2073_, 0, v_env_2067_);
lean_ctor_set(v___x_2073_, 1, v___x_2069_);
lean_ctor_set(v___x_2073_, 2, v___x_2072_);
lean_ctor_set(v___x_2073_, 3, v_options_2068_);
v___x_2074_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v_msgData_2062_);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0___boxed(lean_object* v_msgData_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msgData_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(lean_object* v_msg_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_ref_2085_; lean_object* v___x_2086_; lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2095_; 
v_ref_2085_ = lean_ctor_get(v___y_2082_, 5);
v___x_2086_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msg_2081_, v___y_2082_, v___y_2083_);
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
lean_inc(v_ref_2085_);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v_ref_2085_);
lean_ctor_set(v___x_2091_, 1, v_a_2087_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set_tag(v___x_2089_, 1);
lean_ctor_set(v___x_2089_, 0, v___x_2091_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg___boxed(lean_object* v_msg_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
return v_res_2100_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0));
v___x_2103_ = l_Lean_stringToMessageData(v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(lean_object* v_ps_2104_, lean_object* v_i_2105_, lean_object* v_type_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = lean_array_get_size(v_ps_2104_);
v___x_2111_ = lean_nat_dec_lt(v_i_2105_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
lean_dec(v_i_2105_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_type_2106_);
return v___x_2112_;
}
else
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_Expr_headBeta(v_type_2106_);
if (lean_obj_tag(v___x_2113_) == 7)
{
lean_object* v_body_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_body_2114_ = lean_ctor_get(v___x_2113_, 2);
lean_inc_ref(v_body_2114_);
lean_dec_ref(v___x_2113_);
v___x_2115_ = lean_unsigned_to_nat(1u);
v___x_2116_ = lean_nat_add(v_i_2105_, v___x_2115_);
v___x_2117_ = lean_array_fget_borrowed(v_ps_2104_, v_i_2105_);
lean_dec(v_i_2105_);
v___x_2118_ = lean_expr_instantiate1(v_body_2114_, v___x_2117_);
lean_dec_ref(v_body_2114_);
v_i_2105_ = v___x_2116_;
v_type_2106_ = v___x_2118_;
goto _start;
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v___x_2113_);
lean_dec(v_i_2105_);
v___x_2120_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1, &l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1);
v___x_2121_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v___x_2120_, v_a_2107_, v_a_2108_);
return v___x_2121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___boxed(lean_object* v_ps_2122_, lean_object* v_i_2123_, lean_object* v_type_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2122_, v_i_2123_, v_type_2124_, v_a_2125_, v_a_2126_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec_ref(v_ps_2122_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(lean_object* v_00_u03b1_2129_, lean_object* v_msg_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_2130_, v___y_2131_, v___y_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_msg_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(v_00_u03b1_2135_, v_msg_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter___redArg(lean_object* v_e_2141_, lean_object* v_h__1_2142_, lean_object* v_h__2_2143_){
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
lean_dec_ref(v_e_2141_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter(lean_object* v_motive_2151_, lean_object* v_e_2152_, lean_object* v_h__1_2153_, lean_object* v_h__2_2154_){
_start:
{
if (lean_obj_tag(v_e_2152_) == 7)
{
lean_object* v_binderName_2155_; lean_object* v_binderType_2156_; lean_object* v_body_2157_; uint8_t v_binderInfo_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v_h__2_2154_);
v_binderName_2155_ = lean_ctor_get(v_e_2152_, 0);
lean_inc(v_binderName_2155_);
v_binderType_2156_ = lean_ctor_get(v_e_2152_, 1);
lean_inc_ref(v_binderType_2156_);
v_body_2157_ = lean_ctor_get(v_e_2152_, 2);
lean_inc_ref(v_body_2157_);
v_binderInfo_2158_ = lean_ctor_get_uint8(v_e_2152_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2152_);
v___x_2159_ = lean_box(v_binderInfo_2158_);
v___x_2160_ = lean_apply_4(v_h__1_2153_, v_binderName_2155_, v_binderType_2156_, v_body_2157_, v___x_2159_);
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; 
lean_dec(v_h__1_2153_);
v___x_2161_ = lean_apply_2(v_h__2_2154_, v_e_2152_, lean_box(0));
return v___x_2161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object* v_type_2162_, lean_object* v_ps_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = lean_unsigned_to_nat(0u);
v___x_2168_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(v_ps_2163_, v___x_2167_, v_type_2162_, v_a_2164_, v_a_2165_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateForall___boxed(lean_object* v_type_2169_, lean_object* v_ps_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_2169_, v_ps_2170_, v_a_2171_, v_a_2172_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
lean_dec_ref(v_ps_2170_);
return v_res_2174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object* v_type_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Expr_headBeta(v_type_2175_);
switch(lean_obj_tag(v___x_2176_))
{
case 3:
{
lean_object* v_u_2177_; 
v_u_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_u_2177_);
lean_dec_ref(v___x_2176_);
if (lean_obj_tag(v_u_2177_) == 0)
{
uint8_t v___x_2178_; 
v___x_2178_ = 1;
return v___x_2178_;
}
else
{
uint8_t v___x_2179_; 
lean_dec(v_u_2177_);
v___x_2179_ = 0;
return v___x_2179_;
}
}
case 7:
{
lean_object* v_body_2180_; 
v_body_2180_ = lean_ctor_get(v___x_2176_, 2);
lean_inc_ref(v_body_2180_);
lean_dec_ref(v___x_2176_);
v_type_2175_ = v_body_2180_;
goto _start;
}
default: 
{
uint8_t v___x_2182_; 
lean_dec_ref(v___x_2176_);
v___x_2182_ = 0;
return v___x_2182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isPredicateType___boxed(lean_object* v_type_2183_){
_start:
{
uint8_t v_res_2184_; lean_object* v_r_2185_; 
v_res_2184_ = l_Lean_Compiler_LCNF_isPredicateType(v_type_2183_);
v_r_2185_ = lean_box(v_res_2184_);
return v_r_2185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_maybeTypeFormerType(lean_object* v_type_2186_){
_start:
{
lean_object* v___x_2187_; 
lean_inc_ref(v_type_2186_);
v___x_2187_ = l_Lean_Expr_headBeta(v_type_2186_);
switch(lean_obj_tag(v___x_2187_))
{
case 3:
{
uint8_t v___x_2188_; 
lean_dec_ref(v___x_2187_);
lean_dec_ref(v_type_2186_);
v___x_2188_ = 1;
return v___x_2188_;
}
case 7:
{
lean_object* v_body_2189_; 
lean_dec_ref(v_type_2186_);
v_body_2189_ = lean_ctor_get(v___x_2187_, 2);
lean_inc_ref(v_body_2189_);
lean_dec_ref(v___x_2187_);
v_type_2186_ = v_body_2189_;
goto _start;
}
default: 
{
uint8_t v___x_2191_; 
lean_dec_ref(v___x_2187_);
v___x_2191_ = l_Lean_Expr_isErased(v_type_2186_);
lean_dec_ref(v_type_2186_);
return v___x_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_maybeTypeFormerType___boxed(lean_object* v_type_2192_){
_start:
{
uint8_t v_res_2193_; lean_object* v_r_2194_; 
v_res_2193_ = l_Lean_Compiler_LCNF_maybeTypeFormerType(v_type_2192_);
v_r_2194_ = lean_box(v_res_2193_);
return v_r_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object* v_type_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Expr_getAppFn(v_type_2195_);
if (lean_obj_tag(v___x_2198_) == 4)
{
lean_object* v_declName_2199_; lean_object* v___x_2200_; lean_object* v_env_2201_; uint8_t v___x_2202_; 
v_declName_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_declName_2199_);
lean_dec_ref(v___x_2198_);
v___x_2200_ = lean_st_ref_get(v_a_2196_);
v_env_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc_ref(v_env_2201_);
lean_dec(v___x_2200_);
lean_inc(v_declName_2199_);
v___x_2202_ = lean_is_class(v_env_2201_, v_declName_2199_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v_declName_2199_);
v___x_2203_ = lean_box(0);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2205_, 0, v_declName_2199_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v___x_2198_);
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg___boxed(lean_object* v_type_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2209_, v_a_2210_);
lean_dec(v_a_2210_);
lean_dec_ref(v_type_2209_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object* v_type_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2213_, v_a_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isClass_x3f___boxed(lean_object* v_type_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Compiler_LCNF_isClass_x3f(v_type_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec_ref(v_type_2218_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object* v_type_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v___x_2226_; 
lean_inc_ref(v_type_2223_);
v___x_2226_ = l_Lean_Expr_headBeta(v_type_2223_);
if (lean_obj_tag(v___x_2226_) == 7)
{
lean_object* v_body_2227_; 
lean_dec_ref(v_type_2223_);
v_body_2227_ = lean_ctor_get(v___x_2226_, 2);
lean_inc_ref(v_body_2227_);
lean_dec_ref(v___x_2226_);
v_type_2223_ = v_body_2227_;
goto _start;
}
else
{
lean_object* v___x_2229_; 
lean_dec_ref(v___x_2226_);
v___x_2229_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2223_, v_a_2224_);
lean_dec_ref(v_type_2223_);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg___boxed(lean_object* v_type_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2230_, v_a_2231_);
lean_dec(v_a_2231_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f(lean_object* v_type_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_2234_, v_a_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___boxed(lean_object* v_type_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Compiler_LCNF_isArrowClass_x3f(v_type_2239_, v_a_2240_, v_a_2241_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object* v_e_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_Expr_headBeta(v_e_2244_);
if (lean_obj_tag(v___x_2245_) == 7)
{
lean_object* v_body_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_body_2246_ = lean_ctor_get(v___x_2245_, 2);
lean_inc_ref(v_body_2246_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = l_Lean_Compiler_LCNF_getArrowArity(v_body_2246_);
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_nat_add(v___x_2247_, v___x_2248_);
lean_dec(v___x_2247_);
return v___x_2249_;
}
else
{
lean_object* v___x_2250_; 
lean_dec_ref(v___x_2245_);
v___x_2250_ = lean_unsigned_to_nat(0u);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object* v_type_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_Expr_getAppFn(v_type_2251_);
if (lean_obj_tag(v___x_2258_) == 4)
{
lean_object* v_declName_2259_; lean_object* v___x_2260_; lean_object* v_env_2261_; uint8_t v___x_2262_; lean_object* v___x_2263_; 
v_declName_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_declName_2259_);
lean_dec_ref(v___x_2258_);
v___x_2260_ = lean_st_ref_get(v_a_2252_);
v_env_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc_ref(v_env_2261_);
lean_dec(v___x_2260_);
v___x_2262_ = 0;
v___x_2263_ = l_Lean_Environment_find_x3f(v_env_2261_, v_declName_2259_, v___x_2262_);
if (lean_obj_tag(v___x_2263_) == 1)
{
lean_object* v_val_2264_; 
v_val_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_val_2264_);
lean_dec_ref(v___x_2263_);
if (lean_obj_tag(v_val_2264_) == 5)
{
lean_object* v_val_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2276_; 
v_val_2265_ = lean_ctor_get(v_val_2264_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_val_2264_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2267_ = v_val_2264_;
v_isShared_2268_ = v_isSharedCheck_2276_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_val_2265_);
lean_dec(v_val_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2276_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2269_ = l_Lean_InductiveVal_numCtors(v_val_2265_);
lean_dec_ref(v_val_2265_);
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = lean_nat_dec_eq(v___x_2269_, v___x_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(v___x_2271_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set_tag(v___x_2267_, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2272_);
v___x_2274_ = v___x_2267_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
else
{
lean_dec(v_val_2264_);
goto v___jp_2254_;
}
}
else
{
lean_dec(v___x_2263_);
goto v___jp_2254_;
}
}
else
{
uint8_t v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v___x_2258_);
v___x_2277_ = 0;
v___x_2278_ = lean_box(v___x_2277_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
v___jp_2254_:
{
uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = 0;
v___x_2256_ = lean_box(v___x_2255_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg___boxed(lean_object* v_type_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2280_, v_a_2281_);
lean_dec(v_a_2281_);
lean_dec_ref(v_type_2280_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object* v_type_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_2284_, v_a_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___boxed(lean_object* v_type_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors(v_type_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec_ref(v_type_2289_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object* v_n_2295_){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2297_ = l_Lean_Name_str___override(v_n_2295_, v___x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isBoxedName(lean_object* v_name_2298_){
_start:
{
if (lean_obj_tag(v_name_2298_) == 1)
{
lean_object* v_str_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v_str_2299_ = lean_ctor_get(v_name_2298_, 1);
v___x_2300_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkBoxedName___closed__0));
v___x_2301_ = lean_string_dec_eq(v_str_2299_, v___x_2300_);
return v___x_2301_;
}
else
{
uint8_t v___x_2302_; 
v___x_2302_ = 0;
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isBoxedName___boxed(lean_object* v_name_2303_){
_start:
{
uint8_t v_res_2304_; lean_object* v_r_2305_; 
v_res_2304_ = l_Lean_Compiler_LCNF_isBoxedName(v_name_2303_);
lean_dec(v_name_2303_);
v_r_2305_ = lean_box(v_res_2304_);
return v_r_2305_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_box(0);
v___x_2310_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__1));
v___x_2311_ = l_Lean_Expr_const___override(v___x_2310_, v___x_2309_);
return v___x_2311_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float(void){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2);
return v___x_2312_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_box(0);
v___x_2317_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__1));
v___x_2318_ = l_Lean_Expr_const___override(v___x_2317_, v___x_2316_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_float32(void){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_float32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_float32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2323_ = lean_box(0);
v___x_2324_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1));
v___x_2325_ = l_Lean_Expr_const___override(v___x_2324_, v___x_2323_);
return v___x_2325_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint8(void){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2);
return v___x_2326_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = lean_box(0);
v___x_2331_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1));
v___x_2332_ = l_Lean_Expr_const___override(v___x_2331_, v___x_2330_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint16(void){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2);
return v___x_2333_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_box(0);
v___x_2338_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1));
v___x_2339_ = l_Lean_Expr_const___override(v___x_2338_, v___x_2337_);
return v___x_2339_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint32(void){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = lean_box(0);
v___x_2345_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1));
v___x_2346_ = l_Lean_Expr_const___override(v___x_2345_, v___x_2344_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_uint64(void){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2, &l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = lean_box(0);
v___x_2352_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__1));
v___x_2353_ = l_Lean_Expr_const___override(v___x_2352_, v___x_2351_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_usize(void){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_usize___closed__2, &l_Lean_Compiler_LCNF_ImpureType_usize___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = lean_box(0);
v___x_2356_ = ((lean_object*)(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2));
v___x_2357_ = l_Lean_Expr_const___override(v___x_2356_, v___x_2355_);
return v___x_2357_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_erased(void){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_erased___closed__0, &l_Lean_Compiler_LCNF_ImpureType_erased___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0);
return v___x_2358_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2362_ = lean_box(0);
v___x_2363_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__1));
v___x_2364_ = l_Lean_Expr_const___override(v___x_2363_, v___x_2362_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_object(void){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2365_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1));
v___x_2371_ = l_Lean_Expr_const___override(v___x_2370_, v___x_2369_);
return v___x_2371_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tobject(void){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2372_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = lean_box(0);
v___x_2377_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1));
v___x_2378_ = l_Lean_Expr_const___override(v___x_2377_, v___x_2376_);
return v___x_2378_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_tagged(void){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2379_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = lean_box(0);
v___x_2381_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__1));
v___x_2382_ = l_Lean_Expr_const___override(v___x_2381_, v___x_2380_);
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ImpureType_void(void){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_void___closed__0, &l_Lean_Compiler_LCNF_ImpureType_void___closed__0_once, _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0);
return v___x_2383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object* v_x_2384_){
_start:
{
if (lean_obj_tag(v_x_2384_) == 4)
{
lean_object* v_declName_2385_; 
v_declName_2385_ = lean_ctor_get(v_x_2384_, 0);
if (lean_obj_tag(v_declName_2385_) == 1)
{
lean_object* v_pre_2386_; 
v_pre_2386_ = lean_ctor_get(v_declName_2385_, 0);
if (lean_obj_tag(v_pre_2386_) == 0)
{
lean_object* v_us_2387_; lean_object* v_str_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v_us_2387_ = lean_ctor_get(v_x_2384_, 1);
v_str_2388_ = lean_ctor_get(v_declName_2385_, 1);
v___x_2389_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2390_ = lean_string_dec_eq(v_str_2388_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2392_ = lean_string_dec_eq(v_str_2388_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2394_ = lean_string_dec_eq(v_str_2388_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2396_ = lean_string_dec_eq(v_str_2388_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0));
v___x_2398_ = lean_string_dec_eq(v_str_2388_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2400_ = lean_string_dec_eq(v_str_2388_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_usize___closed__0));
v___x_2402_ = lean_string_dec_eq(v_str_2388_, v___x_2401_);
if (v___x_2402_ == 0)
{
return v___x_2402_;
}
else
{
if (lean_obj_tag(v_us_2387_) == 0)
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
if (lean_obj_tag(v_us_2387_) == 0)
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
if (lean_obj_tag(v_us_2387_) == 0)
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
if (lean_obj_tag(v_us_2387_) == 0)
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
if (lean_obj_tag(v_us_2387_) == 0)
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
if (lean_obj_tag(v_us_2387_) == 0)
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
if (lean_obj_tag(v_us_2387_) == 0)
{
return v___x_2390_;
}
else
{
uint8_t v___x_2403_; 
v___x_2403_ = 0;
return v___x_2403_;
}
}
}
else
{
uint8_t v___x_2404_; 
v___x_2404_ = 0;
return v___x_2404_;
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar___boxed(lean_object* v_x_2407_){
_start:
{
uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_res_2408_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_x_2407_);
lean_dec_ref(v_x_2407_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(lean_object* v_x_2410_){
_start:
{
if (lean_obj_tag(v_x_2410_) == 4)
{
lean_object* v_declName_2411_; 
v_declName_2411_ = lean_ctor_get(v_x_2410_, 0);
if (lean_obj_tag(v_declName_2411_) == 1)
{
lean_object* v_pre_2412_; 
v_pre_2412_ = lean_ctor_get(v_declName_2411_, 0);
if (lean_obj_tag(v_pre_2412_) == 0)
{
lean_object* v_us_2413_; lean_object* v_str_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v_us_2413_ = lean_ctor_get(v_x_2410_, 1);
v_str_2414_ = lean_ctor_get(v_declName_2411_, 1);
v___x_2415_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2416_ = lean_string_dec_eq(v_str_2414_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2418_ = lean_string_dec_eq(v_str_2414_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2420_ = lean_string_dec_eq(v_str_2414_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2422_ = lean_string_dec_eq(v_str_2414_, v___x_2421_);
if (v___x_2422_ == 0)
{
return v___x_2422_;
}
else
{
if (lean_obj_tag(v_us_2413_) == 0)
{
return v___x_2422_;
}
else
{
return v___x_2420_;
}
}
}
else
{
if (lean_obj_tag(v_us_2413_) == 0)
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
if (lean_obj_tag(v_us_2413_) == 0)
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
if (lean_obj_tag(v_us_2413_) == 0)
{
return v___x_2416_;
}
else
{
uint8_t v___x_2423_; 
v___x_2423_ = 0;
return v___x_2423_;
}
}
}
else
{
uint8_t v___x_2424_; 
v___x_2424_ = 0;
return v___x_2424_;
}
}
else
{
uint8_t v___x_2425_; 
v___x_2425_ = 0;
return v___x_2425_;
}
}
else
{
uint8_t v___x_2426_; 
v___x_2426_ = 0;
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj___boxed(lean_object* v_x_2427_){
_start:
{
uint8_t v_res_2428_; lean_object* v_r_2429_; 
v_res_2428_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(v_x_2427_);
lean_dec_ref(v_x_2427_);
v_r_2429_ = lean_box(v_res_2428_);
return v_r_2429_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object* v_x_2430_){
_start:
{
if (lean_obj_tag(v_x_2430_) == 4)
{
lean_object* v_declName_2431_; 
v_declName_2431_ = lean_ctor_get(v_x_2430_, 0);
if (lean_obj_tag(v_declName_2431_) == 1)
{
lean_object* v_pre_2432_; 
v_pre_2432_ = lean_ctor_get(v_declName_2431_, 0);
if (lean_obj_tag(v_pre_2432_) == 0)
{
lean_object* v_us_2433_; lean_object* v_str_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v_us_2433_ = lean_ctor_get(v_x_2430_, 1);
v_str_2434_ = lean_ctor_get(v_declName_2431_, 1);
v___x_2435_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2436_ = lean_string_dec_eq(v_str_2434_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2437_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0));
v___x_2438_ = lean_string_dec_eq(v_str_2434_, v___x_2437_);
if (v___x_2438_ == 0)
{
return v___x_2438_;
}
else
{
if (lean_obj_tag(v_us_2433_) == 0)
{
return v___x_2438_;
}
else
{
return v___x_2436_;
}
}
}
else
{
if (lean_obj_tag(v_us_2433_) == 0)
{
return v___x_2436_;
}
else
{
uint8_t v___x_2439_; 
v___x_2439_ = 0;
return v___x_2439_;
}
}
}
else
{
uint8_t v___x_2440_; 
v___x_2440_ = 0;
return v___x_2440_;
}
}
else
{
uint8_t v___x_2441_; 
v___x_2441_ = 0;
return v___x_2441_;
}
}
else
{
uint8_t v___x_2442_; 
v___x_2442_ = 0;
return v___x_2442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef___boxed(lean_object* v_x_2443_){
_start:
{
uint8_t v_res_2444_; lean_object* v_r_2445_; 
v_res_2444_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_x_2443_);
lean_dec_ref(v_x_2443_);
v_r_2445_ = lean_box(v_res_2444_);
return v_r_2445_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(lean_object* v_x_2446_){
_start:
{
if (lean_obj_tag(v_x_2446_) == 4)
{
lean_object* v_declName_2447_; 
v_declName_2447_ = lean_ctor_get(v_x_2446_, 0);
if (lean_obj_tag(v_declName_2447_) == 1)
{
lean_object* v_pre_2448_; 
v_pre_2448_ = lean_ctor_get(v_declName_2447_, 0);
if (lean_obj_tag(v_pre_2448_) == 0)
{
lean_object* v_us_2449_; lean_object* v_str_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v_us_2449_ = lean_ctor_get(v_x_2446_, 1);
v_str_2450_ = lean_ctor_get(v_declName_2447_, 1);
v___x_2451_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2452_ = lean_string_dec_eq(v_str_2450_, v___x_2451_);
if (v___x_2452_ == 0)
{
return v___x_2452_;
}
else
{
if (lean_obj_tag(v_us_2449_) == 0)
{
return v___x_2452_;
}
else
{
uint8_t v___x_2453_; 
v___x_2453_ = 0;
return v___x_2453_;
}
}
}
else
{
uint8_t v___x_2454_; 
v___x_2454_ = 0;
return v___x_2454_;
}
}
else
{
uint8_t v___x_2455_; 
v___x_2455_ = 0;
return v___x_2455_;
}
}
else
{
uint8_t v___x_2456_; 
v___x_2456_ = 0;
return v___x_2456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef___boxed(lean_object* v_x_2457_){
_start:
{
uint8_t v_res_2458_; lean_object* v_r_2459_; 
v_res_2458_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_x_2457_);
lean_dec_ref(v_x_2457_);
v_r_2459_ = lean_box(v_res_2458_);
return v_r_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object* v_x_2460_){
_start:
{
if (lean_obj_tag(v_x_2460_) == 4)
{
lean_object* v_declName_2467_; 
v_declName_2467_ = lean_ctor_get(v_x_2460_, 0);
if (lean_obj_tag(v_declName_2467_) == 1)
{
lean_object* v_pre_2468_; 
v_pre_2468_ = lean_ctor_get(v_declName_2467_, 0);
if (lean_obj_tag(v_pre_2468_) == 0)
{
lean_object* v_us_2469_; lean_object* v_str_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v_us_2469_ = lean_ctor_get(v_x_2460_, 1);
v_str_2470_ = lean_ctor_get(v_declName_2467_, 1);
v___x_2471_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_object___closed__0));
v___x_2472_ = lean_string_dec_eq(v_str_2470_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2473_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float___closed__0));
v___x_2474_ = lean_string_dec_eq(v_str_2470_, v___x_2473_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2475_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0));
v___x_2476_ = lean_string_dec_eq(v_str_2470_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2477_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0));
v___x_2478_ = lean_string_dec_eq(v_str_2470_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2479_ = ((lean_object*)(l_Lean_Expr_isVoid___closed__0));
v___x_2480_ = lean_string_dec_eq(v_str_2470_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2481_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0));
v___x_2482_ = lean_string_dec_eq(v_str_2470_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2483_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0));
v___x_2484_ = lean_string_dec_eq(v_str_2470_, v___x_2483_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = ((lean_object*)(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0));
v___x_2486_ = lean_string_dec_eq(v_str_2470_, v___x_2485_);
if (v___x_2486_ == 0)
{
goto v___jp_2461_;
}
else
{
if (lean_obj_tag(v_us_2469_) == 0)
{
goto v___jp_2465_;
}
else
{
goto v___jp_2461_;
}
}
}
else
{
if (lean_obj_tag(v_us_2469_) == 0)
{
goto v___jp_2465_;
}
else
{
goto v___jp_2461_;
}
}
}
else
{
if (lean_obj_tag(v_us_2469_) == 0)
{
goto v___jp_2465_;
}
else
{
goto v___jp_2461_;
}
}
}
else
{
if (lean_obj_tag(v_us_2469_) == 0)
{
goto v___jp_2465_;
}
else
{
goto v___jp_2461_;
}
}
}
else
{
if (lean_obj_tag(v_us_2469_) == 0)
{
goto v___jp_2463_;
}
else
{
goto v___jp_2461_;
}
}
}
else
{
if (lean_obj_tag(v_us_2469_) == 0)
{
goto v___jp_2463_;
}
else
{
goto v___jp_2461_;
}
}
}
else
{
if (lean_obj_tag(v_us_2469_) == 0)
{
goto v___jp_2463_;
}
else
{
goto v___jp_2461_;
}
}
}
else
{
if (lean_obj_tag(v_us_2469_) == 0)
{
goto v___jp_2463_;
}
else
{
goto v___jp_2461_;
}
}
}
else
{
goto v___jp_2461_;
}
}
else
{
goto v___jp_2461_;
}
}
else
{
goto v___jp_2461_;
}
v___jp_2461_:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2);
return v___x_2462_;
}
v___jp_2463_:
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_object___closed__2, &l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2);
return v___x_2464_;
}
v___jp_2465_:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_obj_once(&l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2, &l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once, _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2);
return v___x_2466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed___boxed(lean_object* v_x_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_x_2487_);
lean_dec_ref(v_x_2487_);
return v_res_2488_;
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
